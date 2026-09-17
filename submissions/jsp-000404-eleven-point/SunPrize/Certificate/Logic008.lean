import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step47469 (p2005 p2027 p2997 p3016 p3742 p3791 p5503 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19163 : (¬ p2005) ∨ p2027 ∨ p2997 ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3791) ∨ (¬ p5503))
    : (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3791) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19163 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47470 (p2000 p2027 p2563 p2764 p3646 p3904 p4322 p4948 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19164 : (¬ p2000) ∨ p2027 ∨ (¬ p2563) ∨ p2764 ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p2563) ∨ (¬ p3646) ∨ (¬ p3904) ∨ (¬ p4322) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2000 := h2160;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h19164 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47471 (p2027 p2247 p2996 p3379 p3487 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h19165 : p2027 ∨ (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4650))
    : (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3379) ∨ (¬ p3487) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19165 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step47473 (p1995 p2027 p2169 p2363 p3379 p3860 p4261 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19167 : (¬ p1995) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4261))
    : (¬ p2363) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h19167 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47474 (p2027 p2505 p2579 p2588 p3309 p5191 : Prop)
    (h40810 : (¬ p2027))
    (h19169 : p2027 ∨ (¬ p2505) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p5191))
    : (¬ p2505) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3309) ∨ (¬ p5191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2505 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19169 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step47475 (p1994 p2027 p2630 p2688 p2957 p2958 p3172 p3189 p4315 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19170 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2688 ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4315))
    : (¬ p2630) ∨ (¬ p2957) ∨ (¬ p2958) ∨ (¬ p3172) ∨ (¬ p3189) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2688) := h40880;
    (Or.elim h19170 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47476 (p2005 p2027 p2630 p2688 p2992 p3016 p4315 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19171 : (¬ p2005) ∨ p2027 ∨ (¬ p2630) ∨ p2688 ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p4315))
    : (¬ p2630) ∨ (¬ p2992) ∨ (¬ p3016) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h19171 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47477 (p1979 p2027 p2114 p2144 p2156 p2737 p3365 p3952 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19173 : (¬ p1979) ∨ p2027 ∨ p2114 ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3952))
    : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2737) ∨ (¬ p3365) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19173 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47481 (p1994 p2027 p2156 p2766 p3952 p4120 p4347 p4506 p4700 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19179 : (¬ p1994) ∨ p2027 ∨ (¬ p2156) ∨ p2766 ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506) ∨ (¬ p4700))
    : (¬ p2156) ∨ (¬ p3952) ∨ (¬ p4120) ∨ (¬ p4347) ∨ (¬ p4506) ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2766) := h40884;
    (Or.elim h19179 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47482 (p1990 p2997 p3549 p4518 : Prop)
    (h2150 : p1990)
    (h40890 : (¬ p2997))
    (h19180 : (¬ p1990) ∨ p2997 ∨ (¬ p3549) ∨ p4518)
    : (¬ p3549) ∨ p4518 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4518) := (fun h => hn (Or.inr h));
    let u2 : p1990 := h2150;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h19180 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47483 (p2011 p2027 p2148 p3051 p3115 p4129 p4386 p4391 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h19181 : (¬ p2011) ∨ p2027 ∨ p2148 ∨ (¬ p3051) ∨ (¬ p3115) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391))
    : (¬ p3051) ∨ (¬ p3115) ∨ (¬ p4129) ∨ (¬ p4386) ∨ (¬ p4391) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2011 := h2171;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2148) := h40865;
    (Or.elim h19181 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47484 (p1990 p2027 p2284 p3623 p3631 p3821 p4283 p4320 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40903 : (¬ p3623))
    (h19182 : (¬ p1990) ∨ p2027 ∨ (¬ p2284) ∨ p3623 ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320))
    : (¬ p2284) ∨ (¬ p3631) ∨ (¬ p3821) ∨ (¬ p4283) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1990 := h2150;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3623) := h40903;
    (Or.elim h19182 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47487 (p1994 p2027 p2114 p2630 p3037 p3399 p3572 p3954 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19186 : (¬ p1994) ∨ p2027 ∨ p2114 ∨ (¬ p2630) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954))
    : (¬ p2630) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3572) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19186 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47488 (p1980 p2027 p2114 p2797 p3830 p3853 p3954 p4035 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19187 : (¬ p1980) ∨ p2027 ∨ p2114 ∨ (¬ p2797) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3954) ∨ (¬ p4035))
    : (¬ p2797) ∨ (¬ p3830) ∨ (¬ p3853) ∨ (¬ p3954) ∨ (¬ p4035) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1980 := h2140;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19187 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47491 (p2000 p2027 p2579 p2766 p3573 p3979 p4286 p4347 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19190 : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ p2766 ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347))
    : (¬ p2579) ∨ (¬ p3573) ∨ (¬ p3979) ∨ (¬ p4286) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2000 := h2160;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19190 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47496 (p1993 p2027 p2396 p2997 p3166 p3414 p3947 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19197 : (¬ p1993) ∨ p2027 ∨ (¬ p2396) ∨ p2997 ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3947))
    : (¬ p2396) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1993 := h2153;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19197 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47497 (p1997 p2027 p2114 p2542 p2663 p2737 p2811 p3389 p3742 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19198 : (¬ p1997) ∨ p2027 ∨ p2114 ∨ (¬ p2542) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3389) ∨ (¬ p3742))
    : (¬ p2542) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3389) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h19198 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47500 (p1994 p2027 p2264 p2611 p2630 p2807 p3659 p4117 p4357 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19201 : (¬ p1994) ∨ p2027 ∨ (¬ p2264) ∨ p2611 ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3659) ∨ (¬ p4117) ∨ (¬ p4357))
    : (¬ p2264) ∨ (¬ p2630) ∨ (¬ p2807) ∨ (¬ p3659) ∨ (¬ p4117) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2611) := h40877;
    (Or.elim h19201 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47501 (p1982 p2027 p2220 p2323 p2958 p3256 p3969 p5600 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19202 : (¬ p1982) ∨ p2027 ∨ (¬ p2220) ∨ p2323 ∨ (¬ p2958) ∨ (¬ p3256) ∨ (¬ p3969) ∨ (¬ p5600))
    : (¬ p2220) ∨ (¬ p2958) ∨ (¬ p3256) ∨ (¬ p3969) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h19202 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47502 (p1982 p2027 p2611 p2807 p3005 p3256 p3572 p4117 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19203 : (¬ p1982) ∨ p2027 ∨ p2611 ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3572) ∨ (¬ p4117))
    : (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3256) ∨ (¬ p3572) ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h19203 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47503 (p1995 p2027 p2997 p3097 p3379 p3555 p4173 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19204 : (¬ p1995) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4173))
    : (¬ p3097) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19204 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47504 (p1995 p2027 p2274 p2498 p2588 p2765 p3379 p3555 p4512 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19205 : (¬ p1995) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2498) ∨ (¬ p2588) ∨ p2765 ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4512))
    : (¬ p2274) ∨ (¬ p2498) ∨ (¬ p2588) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p4512) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1995 := h2155;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2765) := h40883;
    (Or.elim h19205 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47505 (p1994 p2027 p2177 p2630 p2997 p3553 p3572 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19206 : (¬ p1994) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2630) ∨ p2997 ∨ (¬ p3553) ∨ (¬ p3572))
    : (¬ p2177) ∨ (¬ p2630) ∨ (¬ p3553) ∨ (¬ p3572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19206 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47506 (p1994 p2027 p2630 p3177 p3441 p3877 p4181 p5590 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40897 : (¬ p3441))
    (h19207 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3177) ∨ p3441 ∨ (¬ p3877) ∨ (¬ p4181) ∨ (¬ p5590))
    : (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4181) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3441) := h40897;
    (Or.elim h19207 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47507 (p1994 p2202 p3742 p4646 : Prop)
    (h2154 : p1994)
    (h40867 : (¬ p2202))
    (h19208 : (¬ p1994) ∨ p2202 ∨ (¬ p3742) ∨ p4646)
    : (¬ p3742) ∨ p4646 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3742 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4646) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h19208 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47508 (p1995 p2027 p2299 p2633 p3379 p3549 p3591 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19210 : (¬ p1995) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591))
    : (¬ p2299) ∨ (¬ p3379) ∨ (¬ p3549) ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19210 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47510 (p2005 p2027 p2264 p2323 p2807 p3422 p3659 p3686 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19212 : (¬ p2005) ∨ p2027 ∨ (¬ p2264) ∨ p2323 ∨ (¬ p2807) ∨ (¬ p3422) ∨ (¬ p3659) ∨ (¬ p3686))
    : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3422) ∨ (¬ p3659) ∨ (¬ p3686) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h19212 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47511 (p1980 p2027 p2177 p2641 p2996 p2997 p3945 p3947 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19213 : (¬ p1980) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ p2997 ∨ (¬ p3945) ∨ (¬ p3947))
    : (¬ p2177) ∨ (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3945) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1980 := h2140;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h19213 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47512 (p1980 p2027 p2641 p2764 p2996 p3947 p4381 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19214 : (¬ p1980) ∨ p2027 ∨ (¬ p2641) ∨ p2764 ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381))
    : (¬ p2641) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19214 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47513 (p1995 p2027 p2938 p2982 p3379 p3834 p4235 p4388 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19215 : (¬ p1995) ∨ p2027 ∨ p2938 ∨ (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4235) ∨ (¬ p4388))
    : (¬ p2982) ∨ (¬ p3379) ∨ (¬ p3834) ∨ (¬ p4235) ∨ (¬ p4388) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h19215 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47516 (p1998 p2027 p2233 p2437 p2470 p2911 p4256 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19218 : (¬ p1998) ∨ p2027 ∨ p2233 ∨ (¬ p2437) ∨ (¬ p2470) ∨ (¬ p2911) ∨ (¬ p4256))
    : (¬ p2437) ∨ (¬ p2470) ∨ (¬ p2911) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19218 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47517 (p2007 p2027 p2114 p2534 p2737 p2811 p3166 p3256 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19219 : (¬ p2007) ∨ p2027 ∨ p2114 ∨ (¬ p2534) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256))
    : (¬ p2534) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3166) ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2007 := h2167;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19219 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47518 (p1997 p2027 p2114 p2542 p3367 p3641 p4256 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19220 : (¬ p1997) ∨ p2027 ∨ p2114 ∨ (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4256))
    : (¬ p2542) ∨ (¬ p3367) ∨ (¬ p3641) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h19220 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47521 (p1976 p2027 p2104 p2766 p3979 p4347 p5612 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19223 : (¬ p1976) ∨ p2027 ∨ (¬ p2104) ∨ p2766 ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5612))
    : (¬ p2104) ∨ (¬ p3979) ∨ (¬ p4347) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19223 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47522 (p1985 p2027 p2210 p2247 p2688 p3527 p3570 p4431 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19224 : (¬ p1985) ∨ p2027 ∨ (¬ p2210) ∨ (¬ p2247) ∨ p2688 ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431))
    : (¬ p2210) ∨ (¬ p2247) ∨ (¬ p3527) ∨ (¬ p3570) ∨ (¬ p4431) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4431 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19224 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47523 (p2007 p2177 p2997 p4420 : Prop)
    (h2167 : p2007)
    (h40890 : (¬ p2997))
    (h19225 : (¬ p2007) ∨ (¬ p2177) ∨ p2997 ∨ p4420)
    : (¬ p2177) ∨ p4420 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4420) := (fun h => hn (Or.inr h));
    let u2 : p2007 := h2167;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h19225 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47524 (p2023 p2027 p2997 p3440 p3461 p3483 p3822 p4321 : Prop)
    (h2183 : p2023)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19226 : (¬ p2023) ∨ p2027 ∨ p2997 ∨ (¬ p3440) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321))
    : (¬ p3440) ∨ (¬ p3461) ∨ (¬ p3483) ∨ (¬ p3822) ∨ (¬ p4321) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2023 := h2183;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h19226 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47525 (p2005 p2493 p2842 p5214 : Prop)
    (h2165 : p2005)
    (h40885 : (¬ p2842))
    (h19227 : (¬ p2005) ∨ (¬ p2493) ∨ p2842 ∨ p5214)
    : (¬ p2493) ∨ p5214 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2493 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5214) := (fun h => hn (Or.inr h));
    let u2 : p2005 := h2165;
    let u3 : (¬ p2842) := h40885;
    (Or.elim h19227 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47527 (p1994 p2027 p2417 p2727 p2914 p2996 p3947 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19230 : (¬ p1994) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2727) ∨ p2914 ∨ (¬ p2996) ∨ (¬ p3947))
    : (¬ p2417) ∨ (¬ p2727) ∨ (¬ p2996) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h19230 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47531 (p1980 p2622 p2641 p2745 : Prop)
    (h2140 : p1980)
    (h40878 : (¬ p2622))
    (h19234 : (¬ p1980) ∨ p2622 ∨ (¬ p2641) ∨ p2745)
    : (¬ p2641) ∨ p2745 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2745) := (fun h => hn (Or.inr h));
    let u2 : p1980 := h2140;
    let u3 : (¬ p2622) := h40878;
    (Or.elim h19234 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47534 (p1994 p2027 p2764 p3574 p3956 p4347 p4444 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19237 : (¬ p1994) ∨ p2027 ∨ p2764 ∨ (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444))
    : (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3574 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19237 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47538 (p1980 p2027 p2641 p2764 p3662 p4208 p4322 : Prop)
    (h2140 : p1980)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19241 : (¬ p1980) ∨ p2027 ∨ (¬ p2641) ∨ p2764 ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4322))
    : (¬ p2641) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1980 := h2140;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47543 (p2011 p2027 p2563 p2938 p2972 p4173 p4235 : Prop)
    (h2171 : p2011)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19246 : (¬ p2011) ∨ p2027 ∨ (¬ p2563) ∨ p2938 ∨ (¬ p2972) ∨ (¬ p4173) ∨ (¬ p4235))
    : (¬ p2563) ∨ (¬ p2972) ∨ (¬ p4173) ∨ (¬ p4235) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2011 := h2171;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h19246 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47569 (p1981 p2027 p2187 p2323 p2641 p2946 p3662 p3986 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19273 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ p2323 ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986))
    : (¬ p2187) ∨ (¬ p2641) ∨ (¬ p2946) ∨ (¬ p3662) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h19273 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47574 (p1992 p2027 p2764 p3688 p3822 p4107 p4381 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19278 : (¬ p1992) ∨ p2027 ∨ p2764 ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4381))
    : (¬ p3688) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3688 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19278 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47584 (p1990 p2027 p2169 p2191 p2192 p2363 p3692 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19290 : (¬ p1990) ∨ p2027 ∨ p2169 ∨ (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3692))
    : (¬ p2191) ∨ (¬ p2192) ∨ (¬ p2363) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h19290 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47588 (p1979 p2027 p2352 p2387 p2588 p2997 p3952 p4356 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19294 : (¬ p1979) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3952) ∨ (¬ p4356))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p3952) ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h19294 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47590 (p1978 p2027 p2352 p2387 p3128 p3461 p3746 p4198 p4425 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40894 : (¬ p3128))
    (h19296 : (¬ p1978) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2387) ∨ p3128 ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4198) ∨ (¬ p4425))
    : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4198) ∨ (¬ p4425) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1978 := h2138;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3128) := h40894;
    (Or.elim h19296 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47591 (p1998 p2027 p2264 p2699 p3707 p3830 p4429 p5284 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19297 : (¬ p1998) ∨ p2027 ∨ (¬ p2264) ∨ p2699 ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4429) ∨ (¬ p5284))
    : (¬ p2264) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4429) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4429 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h19297 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47592 (p1998 p2027 p2253 p2264 p2699 p3027 p3286 p3848 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19298 : (¬ p1998) ∨ p2027 ∨ (¬ p2253) ∨ (¬ p2264) ∨ p2699 ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p3848))
    : (¬ p2253) ∨ (¬ p2264) ∨ (¬ p3027) ∨ (¬ p3286) ∨ (¬ p3848) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2253 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3848 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h19298 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47593 (p2000 p2027 p2187 p2579 p2997 p3097 p3956 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19299 : (¬ p2000) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2579) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3956))
    : (¬ p2187) ∨ (¬ p2579) ∨ (¬ p3097) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19299 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47598 (p2003 p2247 p2688 p5021 : Prop)
    (h2163 : p2003)
    (h40880 : (¬ p2688))
    (h19305 : (¬ p2003) ∨ (¬ p2247) ∨ p2688 ∨ p5021)
    : (¬ p2247) ∨ p5021 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5021) := (fun h => hn (Or.inr h));
    let u2 : p2003 := h2163;
    let u3 : (¬ p2688) := h40880;
    (Or.elim h19305 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47599 (p1998 p2027 p2247 p2688 p2911 p2922 p3379 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19306 : (¬ p1998) ∨ p2027 ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379))
    : (¬ p2247) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h19306 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47600 (p2000 p2210 p2699 p4202 p5191 : Prop)
    (h2160 : p2000)
    (h40881 : (¬ p2699))
    (h19307 : (¬ p2000) ∨ (¬ p2210) ∨ p2699 ∨ (¬ p4202) ∨ p5191)
    : (¬ p2210) ∨ (¬ p4202) ∨ p5191 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5191) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2000 := h2160;
    let u4 : (¬ p2699) := h40881;
    (Or.elim h19307 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step47601 (p1976 p2027 p2462 p2588 p3055 p3584 p4107 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19308 : (¬ p1976) ∨ p2027 ∨ p2462 ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4107))
    : (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h19308 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47603 (p1994 p2027 p2462 p2578 p2588 p2667 p2727 p4107 p4154 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19310 : (¬ p1994) ∨ p2027 ∨ p2462 ∨ (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4107) ∨ (¬ p4154))
    : (¬ p2578) ∨ (¬ p2588) ∨ (¬ p2667) ∨ (¬ p2727) ∨ (¬ p4107) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2578 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2462) := h40875;
    (Or.elim h19310 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47604 (p1992 p2608 p2699 p5117 p5123 : Prop)
    (h2152 : p1992)
    (h40881 : (¬ p2699))
    (h19311 : (¬ p1992) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p5117) ∨ p5123)
    : (¬ p2608) ∨ (¬ p5117) ∨ p5123 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5123) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1992 := h2152;
    let u4 : (¬ p2699) := h40881;
    (Or.elim h19311 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u4 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step47606 (p2001 p2027 p2622 p2850 p3156 p3212 p3475 p4109 p4208 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40878 : (¬ p2622))
    (h19313 : (¬ p2001) ∨ p2027 ∨ p2622 ∨ (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3475) ∨ (¬ p4109) ∨ (¬ p4208))
    : (¬ p2850) ∨ (¬ p3156) ∨ (¬ p3212) ∨ (¬ p3475) ∨ (¬ p4109) ∨ (¬ p4208) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2001 := h2161;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2622) := h40878;
    (Or.elim h19313 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47607 (p1985 p2027 p2247 p2688 p2891 p3212 p4172 p4363 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19314 : (¬ p1985) ∨ p2027 ∨ (¬ p2247) ∨ p2688 ∨ (¬ p2891) ∨ (¬ p3212) ∨ (¬ p4172) ∨ (¬ p4363))
    : (¬ p2247) ∨ (¬ p2891) ∨ (¬ p3212) ∨ (¬ p4172) ∨ (¬ p4363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19314 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47608 (p1982 p2363 p2997 p4405 : Prop)
    (h2142 : p1982)
    (h40890 : (¬ p2997))
    (h19315 : (¬ p1982) ∨ (¬ p2363) ∨ p2997 ∨ p4405)
    : (¬ p2363) ∨ p4405 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4405) := (fun h => hn (Or.inr h));
    let u2 : p1982 := h2142;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h19315 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47609 (p1994 p2027 p2573 p2633 p3540 p3574 p3644 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19317 : (¬ p1994) ∨ p2027 ∨ (¬ p2573) ∨ p2633 ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3644))
    : (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19317 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47610 (p1994 p2027 p2299 p2573 p2633 p3540 p3574 p3921 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19318 : (¬ p1994) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2573) ∨ p2633 ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3921))
    : (¬ p2299) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p3921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19318 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47613 (p1994 p2027 p2462 p2573 p3540 p3574 p4278 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19321 : (¬ p1994) ∨ p2027 ∨ p2462 ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4278))
    : (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3574) ∨ (¬ p4278) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h19321 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47614 (p1990 p2027 p2619 p2696 p2699 p2743 p2839 p3589 p3988 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19322 : (¬ p1990) ∨ p2027 ∨ (¬ p2619) ∨ (¬ p2696) ∨ p2699 ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3589) ∨ (¬ p3988))
    : (¬ p2619) ∨ (¬ p2696) ∨ (¬ p2743) ∨ (¬ p2839) ∨ (¬ p3589) ∨ (¬ p3988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1990 := h2150;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2699) := h40881;
    (Or.elim h19322 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47616 (p1976 p2027 p2122 p2588 p3055 p3584 p3586 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40901 : (¬ p3586))
    (h19324 : (¬ p1976) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) ∨ p3586)
    : (¬ p2122) ∨ (¬ p2588) ∨ (¬ p3055) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3586) := h40901;
    (Or.elim h19324 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (u6 r5)))))))))))))))

theorem step47617 (p1988 p2027 p2323 p2761 p2901 p2946 p3246 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19325 : (¬ p1988) ∨ p2027 ∨ p2323 ∨ (¬ p2761) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246))
    : (¬ p2761) ∨ (¬ p2901) ∨ (¬ p2946) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h19325 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47618 (p1998 p2027 p2247 p2264 p2688 p3516 p3545 p3947 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19326 : (¬ p1998) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2264) ∨ p2688 ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3947))
    : (¬ p2247) ∨ (¬ p2264) ∨ (¬ p3516) ∨ (¬ p3545) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19326 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47622 (p2006 p2027 p2132 p2766 p3425 p3570 p4169 p4348 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19333 : (¬ p2006) ∨ p2027 ∨ (¬ p2132) ∨ p2766 ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4169) ∨ (¬ p4348))
    : (¬ p2132) ∨ (¬ p3425) ∨ (¬ p3570) ∨ (¬ p4169) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4169 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2006 := h2166;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19333 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47624 (p1978 p2027 p2274 p2313 p2766 p3989 p4198 p4347 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19335 : (¬ p1978) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2313) ∨ p2766 ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4347))
    : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3989) ∨ (¬ p4198) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1978 := h2138;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19335 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47626 (p1978 p2027 p2764 p2860 p3646 p4033 p4191 p4385 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19337 : (¬ p1978) ∨ p2027 ∨ p2764 ∨ (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4385))
    : (¬ p2860) ∨ (¬ p3646) ∨ (¬ p4033) ∨ (¬ p4191) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1978 := h2138;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2764) := h40882;
    (Or.elim h19337 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47628 (p1987 p2027 p2299 p2633 p2957 p3097 p3646 p4315 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19340 : (¬ p1987) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4315))
    : (¬ p2299) ∨ (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19340 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47629 (p1992 p2027 p2363 p2608 p2997 p3325 p3860 p4261 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19341 : (¬ p1992) ∨ p2027 ∨ (¬ p2363) ∨ (¬ p2608) ∨ p2997 ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4261))
    : (¬ p2363) ∨ (¬ p2608) ∨ (¬ p3325) ∨ (¬ p3860) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h19341 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47631 (p2003 p2027 p2122 p2313 p2766 p4138 p4348 p4358 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19343 : (¬ p2003) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2313) ∨ p2766 ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4358))
    : (¬ p2122) ∨ (¬ p2313) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2003 := h2163;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19343 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47632 (p2007 p2027 p2409 p3449 p3452 p4181 p4286 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h19344 : (¬ p2007) ∨ p2027 ∨ p2409 ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4286))
    : (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2007 := h2167;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h19344 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47633 (p2003 p2027 p2299 p2313 p2764 p4348 p4444 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19345 : (¬ p2003) ∨ p2027 ∨ (¬ p2299) ∨ (¬ p2313) ∨ p2764 ∨ (¬ p4348) ∨ (¬ p4444))
    : (¬ p2299) ∨ (¬ p2313) ∨ (¬ p4348) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19345 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47638 (p1992 p2027 p2274 p2608 p2765 p3549 p3591 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19352 : (¬ p1992) ∨ p2027 ∨ (¬ p2274) ∨ (¬ p2608) ∨ p2765 ∨ (¬ p3549) ∨ (¬ p3591))
    : (¬ p2274) ∨ (¬ p2608) ∨ (¬ p3549) ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1992 := h2152;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19352 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47640 (p1981 p2027 p2295 p2323 p2331 p2352 p2588 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19354 : (¬ p1981) ∨ p2027 ∨ (¬ p2295) ∨ p2323 ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p2588))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p2588) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h19354 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47641 (p1992 p2210 p2699 p4377 : Prop)
    (h2152 : p1992)
    (h40881 : (¬ p2699))
    (h19355 : (¬ p1992) ∨ (¬ p2210) ∨ p2699 ∨ p4377)
    : (¬ p2210) ∨ p4377 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4377) := (fun h => hn (Or.inr h));
    let u2 : p1992 := h2152;
    let u3 : (¬ p2699) := h40881;
    (Or.elim h19355 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47642 (p2010 p2765 p4110 p4646 : Prop)
    (h2170 : p2010)
    (h40883 : (¬ p2765))
    (h19356 : (¬ p2010) ∨ p2765 ∨ (¬ p4110) ∨ p4646)
    : (¬ p4110) ∨ p4646 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4110 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4646) := (fun h => hn (Or.inr h));
    let u2 : p2010 := h2170;
    let u3 : (¬ p2765) := h40883;
    (Or.elim h19356 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47643 (p1999 p2027 p2241 p2699 p3506 p3842 p4191 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19357 : (¬ p1999) ∨ p2027 ∨ (¬ p2241) ∨ p2699 ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4191))
    : (¬ p2241) ∨ (¬ p3506) ∨ (¬ p3842) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1999 := h2159;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h19357 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47644 (p1996 p2027 p2233 p2499 p2573 p2934 p3527 p3553 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19358 : (¬ p1996) ∨ p2027 ∨ p2233 ∨ (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3553))
    : (¬ p2499) ∨ (¬ p2573) ∨ (¬ p2934) ∨ (¬ p3527) ∨ (¬ p3553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2934 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1996 := h2156;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h19358 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47645 (p1994 p2027 p2230 p2440 p2633 p3540 p3570 p4001 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19359 : (¬ p1994) ∨ p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ p2633 ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3540) ∨ (¬ p3570) ∨ (¬ p4001) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19359 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47647 (p1981 p2027 p2528 p2914 p3641 p3876 p4347 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19361 : (¬ p1981) ∨ p2027 ∨ (¬ p2528) ∨ p2914 ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4347))
    : (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3876) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h19361 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47652 (p1996 p2027 p2169 p2589 p2608 p2685 p2749 p3842 p3989 p4035 p4110 p5193 : Prop)
    (h2156 : p1996)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19366 : (¬ p1996) ∨ p2027 ∨ p2169 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (¬ p2749) ∨ (¬ p3842) ∨ (¬ p3989) ∨ (¬ p4035) ∨ (¬ p4110) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2685) ∨ (¬ p2749) ∨ (¬ p3842) ∨ (¬ p3989) ∨ (¬ p4035) ∨ (¬ p4110) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p1996 := h2156;
    let u10 : (¬ p2027) := h40810;
    let u11 : (¬ p2169) := h40866;
    (Or.elim h19366 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u10 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u11 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (False.elim (r10 u8)))))))))))))))))))))))))

theorem step47654 (p1994 p2027 p2459 p2630 p2633 p3572 p3857 p3961 p4155 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19368 : (¬ p1994) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p3572) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4155))
    : (¬ p2459) ∨ (¬ p2630) ∨ (¬ p3572) ∨ (¬ p3857) ∨ (¬ p3961) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2633) := h40879;
    (Or.elim h19368 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47657 (p2024 p2027 p2241 p2641 p2699 p3755 p4195 : Prop)
    (h2184 : p2024)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19371 : (¬ p2024) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2641) ∨ p2699 ∨ (¬ p3755) ∨ (¬ p4195))
    : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3755) ∨ (¬ p4195) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2024 := h2184;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h19371 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47658 (p1994 p2027 p2633 p2727 p2957 p3556 p3570 p3662 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19372 : (¬ p1994) ∨ p2027 ∨ p2633 ∨ (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662))
    : (¬ p2727) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19372 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47660 (p1997 p2027 p2230 p2766 p3540 p3644 p4348 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19374 : (¬ p1997) ∨ p2027 ∨ (¬ p2230) ∨ p2766 ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348))
    : (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19374 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47662 (p2004 p2202 p2427 p4911 : Prop)
    (h2164 : p2004)
    (h40867 : (¬ p2202))
    (h19376 : (¬ p2004) ∨ p2202 ∨ (¬ p2427) ∨ p4911)
    : (¬ p2427) ∨ p4911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4911) := (fun h => hn (Or.inr h));
    let u2 : p2004 := h2164;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h19376 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47663 (p1990 p2699 p3093 p4518 : Prop)
    (h2150 : p1990)
    (h40881 : (¬ p2699))
    (h19378 : (¬ p1990) ∨ p2699 ∨ (¬ p3093) ∨ p4518)
    : (¬ p3093) ∨ p4518 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4518) := (fun h => hn (Or.inr h));
    let u2 : p1990 := h2150;
    let u3 : (¬ p2699) := h40881;
    (Or.elim h19378 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47666 (p1990 p2027 p2241 p2295 p2641 p2699 p3097 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19381 : (¬ p1990) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ p2699 ∨ (¬ p3097))
    : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3097) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h19381 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47672 (p1983 p2027 p2177 p2307 p2344 p3246 p3570 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h19387 : (¬ p1983) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ p2344 ∨ (¬ p3246) ∨ (¬ p3570))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3246) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2344) := h40871;
    (Or.elim h19387 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47674 (p1977 p2355 p3662 p4917 : Prop)
    (h2137 : p1977)
    (h40872 : (¬ p2355))
    (h19389 : (¬ p1977) ∨ p2355 ∨ (¬ p3662) ∨ p4917)
    : (¬ p3662) ∨ p4917 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4917) := (fun h => hn (Or.inr h));
    let u2 : p1977 := h2137;
    let u3 : (¬ p2355) := h40872;
    (Or.elim h19389 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47675 (p1994 p2630 p3586 p4842 : Prop)
    (h2154 : p1994)
    (h40901 : (¬ p3586))
    (h19393 : (¬ p1994) ∨ (¬ p2630) ∨ p3586 ∨ p4842)
    : (¬ p2630) ∨ p4842 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4842) := (fun h => hn (Or.inr h));
    let u2 : p1994 := h2154;
    let u3 : (¬ p3586) := h40901;
    (Or.elim h19393 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47679 (p1994 p2027 p2630 p2766 p3553 p3572 p4348 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19400 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ p2766 ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348))
    : (¬ p2630) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19400 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47681 (p1998 p2027 p2114 p2137 p2156 p2177 p2274 p2839 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19402 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839))
    : (¬ p2137) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19402 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47682 (p1984 p2501 p3008 p3591 : Prop)
    (h2144 : p1984)
    (h40891 : (¬ p3008))
    (h19403 : (¬ p1984) ∨ p2501 ∨ p3008 ∨ (¬ p3591))
    : p2501 ∨ (¬ p3591) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2501) := (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p1984 := h2144;
    let u3 : (¬ p3008) := h40891;
    (Or.elim h19403 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step47683 (p2001 p2027 p2641 p2688 p2946 p2963 p3156 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19404 : (¬ p2001) ∨ p2027 ∨ (¬ p2641) ∨ p2688 ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3156))
    : (¬ p2641) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2001 := h2161;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2688) := h40880;
    (Or.elim h19404 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47684 (p1984 p2027 p2191 p2373 p2765 p3555 p4110 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19405 : (¬ p1984) ∨ p2027 ∨ (¬ p2191) ∨ (¬ p2373) ∨ p2765 ∨ (¬ p3555) ∨ (¬ p4110))
    : (¬ p2191) ∨ (¬ p2373) ∨ (¬ p3555) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19405 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47686 (p1995 p2233 p3379 p5190 : Prop)
    (h2155 : p1995)
    (h40868 : (¬ p2233))
    (h19407 : (¬ p1995) ∨ p2233 ∨ (¬ p3379) ∨ p5190)
    : (¬ p3379) ∨ p5190 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5190) := (fun h => hn (Or.inr h));
    let u2 : p1995 := h2155;
    let u3 : (¬ p2233) := h40868;
    (Or.elim h19407 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47688 (p2027 p2313 p2383 p2553 p3324 p4973 : Prop)
    (h40810 : (¬ p2027))
    (h19409 : p2027 ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p3324) ∨ (¬ p4973))
    : (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2553) ∨ (¬ p3324) ∨ (¬ p4973) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19409 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step47691 (p1998 p2027 p2137 p2220 p2938 p3969 p4244 p5558 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19413 : (¬ p1998) ∨ p2027 ∨ (¬ p2137) ∨ (¬ p2220) ∨ p2938 ∨ (¬ p3969) ∨ (¬ p4244) ∨ (¬ p5558))
    : (¬ p2137) ∨ (¬ p2220) ∨ (¬ p3969) ∨ (¬ p4244) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2938) := h40888;
    (Or.elim h19413 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47692 (p1976 p2027 p2476 p2765 p3641 p3684 p3905 p4110 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19415 : (¬ p1976) ∨ p2027 ∨ (¬ p2476) ∨ p2765 ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3905) ∨ (¬ p4110))
    : (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3684) ∨ (¬ p3905) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h19415 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47694 (p1994 p2027 p2765 p3333 p3359 p3684 p4110 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19417 : (¬ p1994) ∨ p2027 ∨ p2765 ∨ (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684) ∨ (¬ p4110))
    : (¬ p3333) ∨ (¬ p3359) ∨ (¬ p3684) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19417 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47696 (p1976 p2027 p2589 p2766 p3692 p3905 p3969 p4286 p4607 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19419 : (¬ p1976) ∨ p2027 ∨ (¬ p2589) ∨ p2766 ∨ (¬ p3692) ∨ (¬ p3905) ∨ (¬ p3969) ∨ (¬ p4286) ∨ (¬ p4607))
    : (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3905) ∨ (¬ p3969) ∨ (¬ p4286) ∨ (¬ p4607) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1976 := h2136;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2766) := h40884;
    (Or.elim h19419 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47697 (p1998 p2027 p2177 p2295 p2765 p3125 p4037 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19420 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ p2765 ∨ (¬ p3125) ∨ (¬ p4037))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3125) ∨ (¬ p4037) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19420 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47700 (p1995 p2027 p2459 p2534 p2633 p3379 p3860 p4370 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19423 : (¬ p1995) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370))
    : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19423 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47701 (p2006 p2323 p2946 p4906 : Prop)
    (h2166 : p2006)
    (h40870 : (¬ p2323))
    (h19424 : (¬ p2006) ∨ p2323 ∨ (¬ p2946) ∨ p4906)
    : (¬ p2946) ∨ p4906 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4906) := (fun h => hn (Or.inr h));
    let u2 : p2006 := h2166;
    let u3 : (¬ p2323) := h40870;
    (Or.elim h19424 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47702 (p1978 p2611 p2946 p2954 p4117 : Prop)
    (h2138 : p1978)
    (h40877 : (¬ p2611))
    (h19425 : (¬ p1978) ∨ p2611 ∨ (¬ p2946) ∨ p2954 ∨ (¬ p4117))
    : (¬ p2946) ∨ p2954 ∨ (¬ p4117) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2954) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1978 := h2138;
    let u4 : (¬ p2611) := h40877;
    (Or.elim h19425 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u1 q3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step47703 (p1994 p2132 p2611 p2630 p4315 p5053 : Prop)
    (h2154 : p1994)
    (h40877 : (¬ p2611))
    (h19426 : (¬ p1994) ∨ (¬ p2132) ∨ p2611 ∨ (¬ p2630) ∨ (¬ p4315) ∨ p5053)
    : (¬ p2132) ∨ (¬ p2630) ∨ (¬ p4315) ∨ p5053 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p5053) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2611) := h40877;
    (Or.elim h19426 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (u3 r4)))))))))))))

theorem step47704 (p1999 p2459 p2633 p4330 : Prop)
    (h2159 : p1999)
    (h40879 : (¬ p2633))
    (h19427 : (¬ p1999) ∨ (¬ p2459) ∨ p2633 ∨ p4330)
    : (¬ p2459) ∨ p4330 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4330) := (fun h => hn (Or.inr h));
    let u2 : p1999 := h2159;
    let u3 : (¬ p2633) := h40879;
    (Or.elim h19427 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47705 (p2025 p2027 p2764 p3555 p3830 p4322 p4363 : Prop)
    (h2185 : p2025)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19428 : (¬ p2025) ∨ p2027 ∨ p2764 ∨ (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4322) ∨ (¬ p4363))
    : (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4322) ∨ (¬ p4363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3555 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2025 := h2185;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19428 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47706 (p1994 p2027 p2630 p3572 p3623 p4075 p4155 p4372 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40903 : (¬ p3623))
    (h19429 : (¬ p1994) ∨ p2027 ∨ (¬ p2630) ∨ (¬ p3572) ∨ p3623 ∨ (¬ p4075) ∨ (¬ p4155) ∨ (¬ p4372))
    : (¬ p2630) ∨ (¬ p3572) ∨ (¬ p4075) ∨ (¬ p4155) ∨ (¬ p4372) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3623) := h40903;
    (Or.elim h19429 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47708 (p1995 p2027 p2766 p3266 p3379 p3440 p3860 p4321 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19431 : (¬ p1995) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4321))
    : (¬ p3266) ∨ (¬ p3379) ∨ (¬ p3440) ∨ (¬ p3860) ∨ (¬ p4321) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19431 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47709 (p1995 p2027 p2766 p3379 p3555 p3692 p3880 p4034 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19433 : (¬ p1995) ∨ p2027 ∨ p2766 ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4034))
    : (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1995 := h2155;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19433 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47711 (p1982 p2027 p2166 p2202 p2427 p3146 p3486 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19435 : (¬ p1982) ∨ p2027 ∨ (¬ p2166) ∨ p2202 ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3486))
    : (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3146) ∨ (¬ p3486) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h19435 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47712 (p1982 p2027 p2688 p2951 p2992 p3146 p3998 p4238 p5568 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19436 : (¬ p1982) ∨ p2027 ∨ p2688 ∨ (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p5568))
    : (¬ p2951) ∨ (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3998) ∨ (¬ p4238) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2951 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1982 := h2142;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2688) := h40880;
    (Or.elim h19436 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47713 (p1997 p2027 p2114 p2542 p2573 p2663 p2737 p2811 p3574 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19438 : (¬ p1997) ∨ p2027 ∨ p2114 ∨ (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3574))
    : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2663) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p3574) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2114) := h40864;
    (Or.elim h19438 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47714 (p1994 p2027 p2459 p2630 p2633 p4118 p4195 p4196 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19440 : (¬ p1994) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196))
    : (¬ p2459) ∨ (¬ p2630) ∨ (¬ p4118) ∨ (¬ p4195) ∨ (¬ p4196) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19440 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47715 (p1994 p2027 p2459 p2630 p2633 p3877 p4118 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19441 : (¬ p1994) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p3877) ∨ (¬ p4118))
    : (¬ p2459) ∨ (¬ p2630) ∨ (¬ p3877) ∨ (¬ p4118) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19441 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47716 (p1997 p2027 p2187 p2542 p2765 p3574 p3956 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19442 : (¬ p1997) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2542) ∨ p2765 ∨ (¬ p3574) ∨ (¬ p3956))
    : (¬ p2187) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19442 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47717 (p1997 p2027 p2187 p2230 p2765 p3540 p3920 p3956 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19443 : (¬ p1997) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ p2765 ∨ (¬ p3540) ∨ (¬ p3920) ∨ (¬ p3956))
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p3540) ∨ (¬ p3920) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3920 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h19443 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47718 (p1975 p2202 p2553 p4717 : Prop)
    (h2135 : p1975)
    (h40867 : (¬ p2202))
    (h19444 : (¬ p1975) ∨ p2202 ∨ (¬ p2553) ∨ p4717)
    : (¬ p2553) ∨ p4717 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4717) := (fun h => hn (Or.inr h));
    let u2 : p1975 := h2135;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h19444 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47721 (p2001 p2534 p2766 p4434 : Prop)
    (h2161 : p2001)
    (h40884 : (¬ p2766))
    (h19447 : (¬ p2001) ∨ (¬ p2534) ∨ p2766 ∨ p4434)
    : (¬ p2534) ∨ p4434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4434) := (fun h => hn (Or.inr h));
    let u2 : p2001 := h2161;
    let u3 : (¬ p2766) := h40884;
    (Or.elim h19447 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47724 (p2010 p2633 p3570 p4277 : Prop)
    (h2170 : p2010)
    (h40879 : (¬ p2633))
    (h19451 : (¬ p2010) ∨ p2633 ∨ (¬ p3570) ∨ p4277)
    : (¬ p3570) ∨ p4277 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3570 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4277) := (fun h => hn (Or.inr h));
    let u2 : p2010 := h2170;
    let u3 : (¬ p2633) := h40879;
    (Or.elim h19451 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47725 (p1994 p2027 p2331 p2630 p2633 p3172 p4195 p4548 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19452 : (¬ p1994) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2630) ∨ p2633 ∨ (¬ p3172) ∨ (¬ p4195) ∨ (¬ p4548))
    : (¬ p2331) ∨ (¬ p2630) ∨ (¬ p3172) ∨ (¬ p4195) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1994 := h2154;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19452 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47729 (p1984 p2027 p2202 p2245 p2563 p2952 p2992 p3745 p4154 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19456 : (¬ p1984) ∨ p2027 ∨ p2202 ∨ (¬ p2245) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154))
    : (¬ p2245) ∨ (¬ p2563) ∨ (¬ p2952) ∨ (¬ p2992) ∨ (¬ p3745) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2202) := h40867;
    (Or.elim h19456 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47730 (p1982 p2027 p2098 p2114 p2138 p2839 p3146 p4188 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19457 : (¬ p1982) ∨ p2027 ∨ (¬ p2098) ∨ p2114 ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p4188))
    : (¬ p2098) ∨ (¬ p2138) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p4188) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2098 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4188 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19457 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47732 (p1984 p2027 p2247 p2459 p2633 p4118 p4360 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19459 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2459) ∨ p2633 ∨ (¬ p4118) ∨ (¬ p4360))
    : (¬ p2247) ∨ (¬ p2459) ∨ (¬ p4118) ∨ (¬ p4360) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19459 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47734 (p1988 p2027 p2114 p2137 p2220 p2839 p3146 p3266 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19461 : (¬ p1988) ∨ p2027 ∨ p2114 ∨ (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p3266))
    : (¬ p2137) ∨ (¬ p2220) ∨ (¬ p2839) ∨ (¬ p3146) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2137 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19461 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47735 (p1991 p2027 p2657 p2964 p3641 p4256 p5160 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40889 : (¬ p2964))
    (h19462 : (¬ p1991) ∨ p2027 ∨ (¬ p2657) ∨ p2964 ∨ (¬ p3641) ∨ (¬ p4256) ∨ (¬ p5160))
    : (¬ p2657) ∨ (¬ p3641) ∨ (¬ p4256) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2964) := h40889;
    (Or.elim h19462 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47737 (p1984 p2027 p2247 p2765 p2881 p2996 p3553 p3872 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19465 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ p2765 ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p3872))
    : (¬ p2247) ∨ (¬ p2881) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p3872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3872 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h19465 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47738 (p1984 p2027 p2247 p2274 p2765 p3568 p4154 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19466 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ (¬ p2274) ∨ p2765 ∨ (¬ p3568) ∨ (¬ p4154))
    : (¬ p2247) ∨ (¬ p2274) ∨ (¬ p3568) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19466 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47740 (p1982 p2938 p3146 p4904 : Prop)
    (h2142 : p1982)
    (h40888 : (¬ p2938))
    (h19468 : (¬ p1982) ∨ p2938 ∨ (¬ p3146) ∨ p4904)
    : (¬ p3146) ∨ p4904 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4904) := (fun h => hn (Or.inr h));
    let u2 : p1982 := h2142;
    let u3 : (¬ p2938) := h40888;
    (Or.elim h19468 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47744 (p1987 p2027 p2104 p2696 p3437 p3537 p3588 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40896 : (¬ p3437))
    (h19474 : (¬ p1987) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p2696) ∨ p3437 ∨ (¬ p3537) ∨ (¬ p3588))
    : (¬ p2104) ∨ (¬ p2696) ∨ (¬ p3537) ∨ (¬ p3588) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3437) := h40896;
    (Or.elim h19474 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47748 (p1988 p2027 p2103 p2459 p3266 p3437 p3537 p3588 p4403 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40896 : (¬ p3437))
    (h19479 : (¬ p1988) ∨ p2027 ∨ (¬ p2103) ∨ (¬ p2459) ∨ (¬ p3266) ∨ p3437 ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4403))
    : (¬ p2103) ∨ (¬ p2459) ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3588) ∨ (¬ p4403) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2103 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1988 := h2148;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3437) := h40896;
    (Or.elim h19479 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47752 (p1993 p2027 p2388 p2657 p2727 p3166 p3662 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h19483 : (¬ p1993) ∨ p2027 ∨ p2388 ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3662))
    : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3166) ∨ (¬ p3662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1993 := h2153;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h19483 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47753 (p1985 p2027 p2352 p2870 p3008 p3758 p3989 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40891 : (¬ p3008))
    (h19484 : (¬ p1985) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2870) ∨ p3008 ∨ (¬ p3758) ∨ (¬ p3989))
    : (¬ p2352) ∨ (¬ p2870) ∨ (¬ p3758) ∨ (¬ p3989) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3008) := h40891;
    (Or.elim h19484 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47755 (p1984 p2027 p2245 p2657 p2727 p2911 p2914 p4360 p4548 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19486 : (¬ p1984) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p4360) ∨ (¬ p4548))
    : (¬ p2245) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2911) ∨ (¬ p4360) ∨ (¬ p4548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2914) := h40887;
    (Or.elim h19486 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u8 q6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47756 (p1982 p2027 p2437 p2528 p2545 p3641 p3876 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19487 : (¬ p1982) ∨ p2027 ∨ (¬ p2437) ∨ (¬ p2528) ∨ p2545 ∨ (¬ p3641) ∨ (¬ p3876))
    : (¬ p2437) ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h19487 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47757 (p2023 p2027 p2202 p3449 p3585 p3684 p3954 : Prop)
    (h2183 : p2023)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19488 : (¬ p2023) ∨ p2027 ∨ p2202 ∨ (¬ p3449) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954))
    : (¬ p3449) ∨ (¬ p3585) ∨ (¬ p3684) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2023 := h2183;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h19488 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47758 (p1996 p2437 p2545 p4327 : Prop)
    (h2156 : p1996)
    (h40876 : (¬ p2545))
    (h19492 : (¬ p1996) ∨ (¬ p2437) ∨ p2545 ∨ p4327)
    : (¬ p2437) ∨ p4327 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4327) := (fun h => hn (Or.inr h));
    let u2 : p1996 := h2156;
    let u3 : (¬ p2545) := h40876;
    (Or.elim h19492 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47759 (p1986 p2027 p2406 p2409 p2589 p3389 p3876 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h19494 : (¬ p1986) ∨ p2027 ∨ (¬ p2406) ∨ p2409 ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876))
    : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h19494 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47764 (p1983 p2027 p2202 p2307 p2396 p2493 p2578 p3238 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19499 : (¬ p1983) ∨ p2027 ∨ p2202 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3238))
    : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p3238) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1983 := h2143;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h19499 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47765 (p1981 p2027 p2187 p2295 p2323 p2946 p3097 p4336 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19500 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2295) ∨ p2323 ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p4336))
    : (¬ p2187) ∨ (¬ p2295) ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1981 := h2141;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h19500 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47766 (p1983 p2027 p2230 p2233 p2982 p3680 p4381 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19501 : (¬ p1983) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4381))
    : (¬ p2230) ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19501 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47767 (p1976 p2027 p2764 p3425 p3659 p4348 p4444 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19502 : (¬ p1976) ∨ p2027 ∨ p2764 ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4444))
    : (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19502 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47768 (p1997 p2027 p2323 p2651 p2850 p3016 p3584 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19503 : (¬ p1997) ∨ p2027 ∨ p2323 ∨ (¬ p2651) ∨ (¬ p2850) ∨ (¬ p3016) ∨ (¬ p3584))
    : (¬ p2651) ∨ (¬ p2850) ∨ (¬ p3016) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2323) := h40870;
    (Or.elim h19503 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47770 (p1999 p2027 p2323 p2651 p3016 p3276 p4191 p4422 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40870 : (¬ p2323))
    (h19506 : (¬ p1999) ∨ p2027 ∨ p2323 ∨ (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422))
    : (¬ p2651) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p4191) ∨ (¬ p4422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1999 := h2159;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2323) := h40870;
    (Or.elim h19506 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47774 (p2010 p2202 p2427 p4277 : Prop)
    (h2170 : p2010)
    (h40867 : (¬ p2202))
    (h19510 : (¬ p2010) ∨ p2202 ∨ (¬ p2427) ∨ p4277)
    : (¬ p2427) ∨ p4277 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4277) := (fun h => hn (Or.inr h));
    let u2 : p2010 := h2170;
    let u3 : (¬ p2202) := h40867;
    (Or.elim h19510 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47775 (p1991 p2027 p2177 p2462 p3414 p3553 p4107 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19512 : (¬ p1991) ∨ p2027 ∨ (¬ p2177) ∨ p2462 ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4107))
    : (¬ p2177) ∨ (¬ p3414) ∨ (¬ p3553) ∨ (¬ p4107) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h19512 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47776 (p1984 p2027 p2245 p2963 p2997 p3063 p3324 p3549 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19513 : (¬ p1984) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2963) ∨ p2997 ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p3549))
    : (¬ p2245) ∨ (¬ p2963) ∨ (¬ p3063) ∨ (¬ p3324) ∨ (¬ p3549) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2997) := h40890;
    (Or.elim h19513 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47779 (p1998 p2027 p2177 p2274 p2331 p2388 p2952 p3986 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h19516 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2331) ∨ p2388 ∨ (¬ p2952) ∨ (¬ p3986))
    : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2388) := h40873;
    (Or.elim h19516 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47782 (p2001 p2027 p2114 p2619 p3830 p3954 p4385 p4387 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19519 : (¬ p2001) ∨ p2027 ∨ p2114 ∨ (¬ p2619) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p4387))
    : (¬ p2619) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4385) ∨ (¬ p4387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19519 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47783 (p1988 p2027 p2122 p2396 p2611 p2761 p2774 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19520 : (¬ p1988) ∨ p2027 ∨ (¬ p2122) ∨ (¬ p2396) ∨ p2611 ∨ (¬ p2761) ∨ (¬ p2774))
    : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h19520 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47785 (p1984 p2027 p2766 p3266 p3817 p4366 p4381 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19522 : (¬ p1984) ∨ p2027 ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381))
    : (¬ p3266) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19522 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47787 (p1975 p2295 p3818 p4761 : Prop)
    (h2135 : p1975)
    (h40905 : (¬ p3818))
    (h19524 : (¬ p1975) ∨ (¬ p2295) ∨ p3818 ∨ p4761)
    : (¬ p2295) ∨ p4761 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4761) := (fun h => hn (Or.inr h));
    let u2 : p1975 := h2135;
    let u3 : (¬ p3818) := h40905;
    (Or.elim h19524 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47792 (p1998 p2027 p2114 p2177 p2274 p2839 p2860 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19531 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839) ∨ (¬ p2860))
    : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2839) ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2839 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h19531 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47793 (p1977 p2027 p2241 p2509 p2534 p2766 p3452 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19532 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2509) ∨ (¬ p2534) ∨ p2766 ∨ (¬ p3452))
    : (¬ p2241) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19532 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47794 (p1975 p2027 p2287 p2299 p2341 p3027 p4066 p4154 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h19533 : (¬ p1975) ∨ p2027 ∨ p2287 ∨ (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4154))
    : (¬ p2299) ∨ (¬ p2341) ∨ (¬ p3027) ∨ (¬ p4066) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2287) := h40869;
    (Or.elim h19533 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47795 (p1991 p2027 p2534 p2657 p2727 p2766 p4360 p4437 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19534 : (¬ p1991) ∨ p2027 ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2727) ∨ p2766 ∨ (¬ p4360) ∨ (¬ p4437))
    : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1991 := h2151;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19534 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47797 (p1984 p2027 p2245 p2518 p2657 p2914 p3590 p3876 p4256 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19536 : (¬ p1984) ∨ p2027 ∨ (¬ p2245) ∨ (¬ p2518) ∨ (¬ p2657) ∨ p2914 ∨ (¬ p3590) ∨ (¬ p3876) ∨ (¬ p4256))
    : (¬ p2245) ∨ (¬ p2518) ∨ (¬ p2657) ∨ (¬ p3590) ∨ (¬ p3876) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2245 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1984 := h2144;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2914) := h40887;
    (Or.elim h19536 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u8 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47798 (p1988 p2027 p2307 p2396 p2641 p2688 p2761 p3567 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19538 : (¬ p1988) ∨ p2027 ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2641) ∨ p2688 ∨ (¬ p2761) ∨ (¬ p3567))
    : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2641) ∨ (¬ p2761) ∨ (¬ p3567) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19538 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47799 (p1983 p2027 p2143 p2284 p2388 p2396 p2870 p3646 p4140 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h19539 : (¬ p1983) ∨ p2027 ∨ (¬ p2143) ∨ (¬ p2284) ∨ p2388 ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p4140))
    : (¬ p2143) ∨ (¬ p2284) ∨ (¬ p2396) ∨ (¬ p2870) ∨ (¬ p3646) ∨ (¬ p4140) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2143 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1983 := h2143;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2388) := h40873;
    (Or.elim h19539 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47801 (p1991 p2027 p2766 p3172 p3692 p3969 p5600 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19541 : (¬ p1991) ∨ p2027 ∨ p2766 ∨ (¬ p3172) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5600))
    : (¬ p3172) ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p5600) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3172 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5600 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19541 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47802 (p1993 p2027 p2191 p2766 p2952 p3166 p3692 p4282 : Prop)
    (h2153 : p1993)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19542 : (¬ p1993) ∨ p2027 ∨ (¬ p2191) ∨ p2766 ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3692) ∨ (¬ p4282))
    : (¬ p2191) ∨ (¬ p2952) ∨ (¬ p3166) ∨ (¬ p3692) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2191 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1993 := h2153;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19542 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47804 (p2001 p2027 p2166 p2542 p2545 p3212 p4109 p4363 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19544 : (¬ p2001) ∨ p2027 ∨ (¬ p2166) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p3212) ∨ (¬ p4109) ∨ (¬ p4363))
    : (¬ p2166) ∨ (¬ p2542) ∨ (¬ p3212) ∨ (¬ p4109) ∨ (¬ p4363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19544 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47805 (p1975 p2027 p2299 p2765 p2870 p2881 p3758 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19545 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2765 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758))
    : (¬ p2299) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3758) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19545 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47807 (p2004 p2027 p2462 p2761 p3399 p3834 p4321 : Prop)
    (h2164 : p2004)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19548 : (¬ p2004) ∨ p2027 ∨ p2462 ∨ (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4321))
    : (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3834) ∨ (¬ p4321) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2004 := h2164;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2462) := h40875;
    (Or.elim h19548 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47808 (p1975 p2027 p2274 p2388 p2860 p3115 p4385 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h19549 : (¬ p1975) ∨ p2027 ∨ (¬ p2274) ∨ p2388 ∨ (¬ p2860) ∨ (¬ p3115) ∨ (¬ p4385))
    : (¬ p2274) ∨ (¬ p2860) ∨ (¬ p3115) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h19549 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47809 (p1977 p2027 p2241 p2417 p2914 p3817 p4366 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19550 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2417) ∨ p2914 ∨ (¬ p3817) ∨ (¬ p4366))
    : (¬ p2241) ∨ (¬ p2417) ∨ (¬ p3817) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h19550 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47810 (p1975 p2027 p2299 p2344 p2717 p3426 p3654 p3917 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40871 : (¬ p2344))
    (h19551 : (¬ p1975) ∨ p2027 ∨ (¬ p2299) ∨ p2344 ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3654) ∨ (¬ p3917))
    : (¬ p2299) ∨ (¬ p2717) ∨ (¬ p3426) ∨ (¬ p3654) ∨ (¬ p3917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2344) := h40871;
    (Or.elim h19551 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47816 (p1975 p2307 p2782 p3586 : Prop)
    (h2135 : p1975)
    (h40901 : (¬ p3586))
    (h19557 : (¬ p1975) ∨ (¬ p2307) ∨ p2782 ∨ p3586)
    : (¬ p2307) ∨ p2782 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2782) := (fun h => hn (Or.inr h));
    let u2 : p1975 := h2135;
    let u3 : (¬ p3586) := h40901;
    (Or.elim h19557 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step47817 (p1991 p2027 p2202 p2440 p2810 p3005 p3172 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19558 : (¬ p1991) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172))
    : (¬ p2440) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2202) := h40867;
    (Or.elim h19558 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47818 (p1998 p2545 p3083 p4438 : Prop)
    (h2158 : p1998)
    (h40876 : (¬ p2545))
    (h19559 : (¬ p1998) ∨ p2545 ∨ (¬ p3083) ∨ p4438)
    : (¬ p3083) ∨ p4438 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4438) := (fun h => hn (Or.inr h));
    let u2 : p1998 := h2158;
    let u3 : (¬ p2545) := h40876;
    (Or.elim h19559 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47821 (p1985 p2027 p2156 p2542 p2545 p2891 p4109 p4173 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19562 : (¬ p1985) ∨ p2027 ∨ (¬ p2156) ∨ (¬ p2542) ∨ p2545 ∨ (¬ p2891) ∨ (¬ p4109) ∨ (¬ p4173))
    : (¬ p2156) ∨ (¬ p2542) ∨ (¬ p2891) ∨ (¬ p4109) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2542 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1985 := h2145;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19562 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47824 (p1998 p2027 p2202 p2440 p2475 p3083 p3998 p5558 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19567 : (¬ p1998) ∨ p2027 ∨ p2202 ∨ (¬ p2440) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3998) ∨ (¬ p5558))
    : (¬ p2440) ∨ (¬ p2475) ∨ (¬ p3083) ∨ (¬ p3998) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h19567 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47825 (p1998 p2027 p2144 p2611 p2870 p2881 p3212 p4385 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19568 : (¬ p1998) ∨ p2027 ∨ (¬ p2144) ∨ p2611 ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3212) ∨ (¬ p4385))
    : (¬ p2144) ∨ (¬ p2870) ∨ (¬ p2881) ∨ (¬ p3212) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h19568 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47826 (p2000 p2027 p2579 p2766 p3266 p3322 p3956 p4191 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19569 : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ p2766 ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3956) ∨ (¬ p4191))
    : (¬ p2579) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3956) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2000 := h2160;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19569 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47827 (p2000 p2027 p2579 p2766 p3266 p4137 p4191 : Prop)
    (h2160 : p2000)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19570 : (¬ p2000) ∨ p2027 ∨ (¬ p2579) ∨ p2766 ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191))
    : (¬ p2579) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2000 := h2160;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19570 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47829 (p2020 p2027 p2144 p2611 p2619 p3051 p3969 p4244 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19572 : (¬ p2020) ∨ p2027 ∨ (¬ p2144) ∨ p2611 ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3969) ∨ (¬ p4244))
    : (¬ p2144) ∨ (¬ p2619) ∨ (¬ p3051) ∨ (¬ p3969) ∨ (¬ p4244) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2020 := h2180;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2611) := h40877;
    (Or.elim h19572 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47832 (p1984 p2027 p2534 p2766 p3860 p4149 p5693 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19575 : (¬ p1984) ∨ p2027 ∨ (¬ p2534) ∨ p2766 ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693))
    : (¬ p2534) ∨ (¬ p3860) ∨ (¬ p4149) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4149 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19575 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47835 (p1988 p2027 p2761 p2873 p3399 p3555 p3631 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h19578 : (¬ p1988) ∨ p2027 ∨ (¬ p2761) ∨ p2873 ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631))
    : (¬ p2761) ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2873) := h40886;
    (Or.elim h19578 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47837 (p1989 p2027 p2352 p2588 p2997 p3989 p4173 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19580 : (¬ p1989) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3989) ∨ (¬ p4173))
    : (¬ p2352) ∨ (¬ p2588) ∨ (¬ p3989) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1989 := h2149;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19580 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47839 (p1991 p2027 p2169 p2363 p2534 p2657 p4256 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19582 : (¬ p1991) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h19582 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47840 (p1988 p2027 p2202 p2427 p2761 p2972 p3556 p3645 p4135 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19583 : (¬ p1988) ∨ p2027 ∨ p2202 ∨ (¬ p2427) ∨ (¬ p2761) ∨ (¬ p2972) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4135))
    : (¬ p2427) ∨ (¬ p2761) ∨ (¬ p2972) ∨ (¬ p3556) ∨ (¬ p3645) ∨ (¬ p4135) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4135 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1988 := h2148;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2202) := h40867;
    (Or.elim h19583 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47842 (p1998 p2027 p2148 p2156 p2427 p2881 p4110 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h19585 : (¬ p1998) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4110))
    : (¬ p2156) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h19585 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47843 (p1976 p2027 p2685 p2766 p3414 p3877 p4118 p4236 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19586 : (¬ p1976) ∨ p2027 ∨ (¬ p2685) ∨ p2766 ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4236))
    : (¬ p2685) ∨ (¬ p3414) ∨ (¬ p3877) ∨ (¬ p4118) ∨ (¬ p4236) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1976 := h2136;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19586 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47845 (p2020 p2027 p2187 p2230 p2545 p2563 p2810 p3005 p3172 p3366 p3519 p3979 p4236 p4376 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19588 : (¬ p2020) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ p2545 ∨ (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4376))
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3979) ∨ (¬ p4236) ∨ (¬ p4376) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p2020 := h2180;
    let u12 : (¬ p2027) := h40810;
    let u13 : (¬ p2545) := h40876;
    (Or.elim h19588 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u12 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u13 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (Or.elim r11 (fun q12 => (False.elim (q12 u9))) (fun r12 => (False.elim (r12 u10)))))))))))))))))))))))))))))

theorem step47846 (p1981 p2027 p2187 p2233 p2553 p2573 p3097 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19589 : (¬ p1981) ∨ p2027 ∨ (¬ p2187) ∨ p2233 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3097))
    : (¬ p2187) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3097) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19589 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47850 (p1992 p2027 p2545 p2608 p2810 p3755 p3834 p3847 : Prop)
    (h2152 : p1992)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19593 : (¬ p1992) ∨ p2027 ∨ p2545 ∨ (¬ p2608) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847))
    : (¬ p2608) ∨ (¬ p2810) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1992 := h2152;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19593 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47851 (p2020 p2027 p2148 p2156 p2373 p3969 p4110 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h19594 : (¬ p2020) ∨ p2027 ∨ p2148 ∨ (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p4110))
    : (¬ p2156) ∨ (¬ p2373) ∨ (¬ p3969) ∨ (¬ p4110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2148) := h40865;
    (Or.elim h19594 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47852 (p1975 p2027 p2331 p2553 p2657 p2688 p2727 p3984 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19595 : (¬ p1975) ∨ p2027 ∨ (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2657) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p3984))
    : (¬ p2331) ∨ (¬ p2553) ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p3984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19595 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47854 (p1977 p2027 p2241 p2284 p2388 p3555 p4173 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40873 : (¬ p2388))
    (h19598 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ (¬ p2284) ∨ p2388 ∨ (¬ p3555) ∨ (¬ p4173))
    : (¬ p2241) ∨ (¬ p2284) ∨ (¬ p3555) ∨ (¬ p4173) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2388) := h40873;
    (Or.elim h19598 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47855 (p1977 p2027 p2241 p2766 p3412 p3497 p3555 p3692 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19599 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ p2766 ∨ (¬ p3412) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p3692))
    : (¬ p2241) ∨ (¬ p3412) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h19599 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47858 (p1977 p2027 p2169 p2241 p2363 p3860 p4261 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19602 : (¬ p1977) ∨ p2027 ∨ p2169 ∨ (¬ p2241) ∨ (¬ p2363) ∨ (¬ p3860) ∨ (¬ p4261))
    : (¬ p2241) ∨ (¬ p2363) ∨ (¬ p3860) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h19602 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47859 (p2023 p2027 p2355 p3005 p3171 p3572 p3998 p5693 : Prop)
    (h2183 : p2023)
    (h40810 : (¬ p2027))
    (h40872 : (¬ p2355))
    (h19603 : (¬ p2023) ∨ p2027 ∨ p2355 ∨ (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3572) ∨ (¬ p3998) ∨ (¬ p5693))
    : (¬ p3005) ∨ (¬ p3171) ∨ (¬ p3572) ∨ (¬ p3998) ∨ (¬ p5693) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2023 := h2183;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2355) := h40872;
    (Or.elim h19603 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47862 (p1998 p2027 p2417 p2881 p2997 p3365 p3389 p3568 p3690 p4195 p4419 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19606 : (¬ p1998) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2881) ∨ p2997 ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4195) ∨ (¬ p4419))
    : (¬ p2417) ∨ (¬ p2881) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3690) ∨ (¬ p4195) ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1998 := h2158;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2997) := h40890;
    (Or.elim h19606 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u10 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step47864 (p1991 p2027 p2766 p2963 p3266 p4037 p4191 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19608 : (¬ p1991) ∨ p2027 ∨ p2766 ∨ (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4037) ∨ (¬ p4191))
    : (¬ p2963) ∨ (¬ p3266) ∨ (¬ p4037) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19608 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47865 (p1977 p2027 p2241 p2766 p3591 p3923 p4347 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19609 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ p2766 ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347))
    : (¬ p2241) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19609 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47866 (p1977 p2027 p2241 p2764 p3860 p4261 p4444 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19610 : (¬ p1977) ∨ p2027 ∨ (¬ p2241) ∨ p2764 ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444))
    : (¬ p2241) ∨ (¬ p3860) ∨ (¬ p4261) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1977 := h2137;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19610 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47869 (p2018 p2027 p2341 p2462 p3543 p3817 p3941 p5612 : Prop)
    (h2178 : p2018)
    (h40810 : (¬ p2027))
    (h40875 : (¬ p2462))
    (h19613 : (¬ p2018) ∨ p2027 ∨ (¬ p2341) ∨ p2462 ∨ (¬ p3543) ∨ (¬ p3817) ∨ (¬ p3941) ∨ (¬ p5612))
    : (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3817) ∨ (¬ p3941) ∨ (¬ p5612) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5612 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2018 := h2178;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2462) := h40875;
    (Or.elim h19613 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47870 (p2001 p2027 p2148 p3212 p4019 p4385 p4744 p5568 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40865 : (¬ p2148))
    (h19614 : (¬ p2001) ∨ p2027 ∨ p2148 ∨ (¬ p3212) ∨ (¬ p4019) ∨ (¬ p4385) ∨ (¬ p4744) ∨ (¬ p5568))
    : (¬ p3212) ∨ (¬ p4019) ∨ (¬ p4385) ∨ (¬ p4744) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3212 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2148) := h40865;
    (Or.elim h19614 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47876 (p1990 p2027 p2545 p2563 p2850 p3343 p5160 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19620 : (¬ p1990) ∨ p2027 ∨ p2545 ∨ (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3343) ∨ (¬ p5160))
    : (¬ p2563) ∨ (¬ p2850) ∨ (¬ p3343) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h19620 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47879 (p2012 p2027 p2764 p2963 p3333 p3362 p3389 p3686 p3868 p4037 p4191 p4423 p4789 : Prop)
    (h2172 : p2012)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19623 : (¬ p2012) ∨ p2027 ∨ p2764 ∨ (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3686) ∨ (¬ p3868) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4423) ∨ (¬ p4789))
    : (¬ p2963) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3686) ∨ (¬ p3868) ∨ (¬ p4037) ∨ (¬ p4191) ∨ (¬ p4423) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4423 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2012 := h2172;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2764) := h40882;
    (Or.elim h19623 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u12 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step47880 (p1998 p2027 p2753 p2764 p2881 p3093 p3362 p3389 p3834 p3868 p4321 p4870 p5660 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19624 : (¬ p1998) ∨ p2027 ∨ (¬ p2753) ∨ p2764 ∨ (¬ p2881) ∨ (¬ p3093) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4870) ∨ (¬ p5660))
    : (¬ p2753) ∨ (¬ p2881) ∨ (¬ p3093) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3834) ∨ (¬ p3868) ∨ (¬ p4321) ∨ (¬ p4870) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3868 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p1998 := h2158;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2764) := h40882;
    (Or.elim h19624 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u12 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step47884 (p2020 p2027 p2230 p2233 p2427 p2881 p3941 : Prop)
    (h2180 : p2020)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19628 : (¬ p2020) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3941))
    : (¬ p2230) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3941) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2020 := h2180;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19628 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47885 (p1998 p2027 p2699 p2881 p3399 p4075 p5660 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h19629 : (¬ p1998) ∨ p2027 ∨ p2699 ∨ (¬ p2881) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5660))
    : (¬ p2881) ∨ (¬ p3399) ∨ (¬ p4075) ∨ (¬ p5660) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h19629 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47886 (p2005 p2027 p2287 p2295 p2313 p3654 p4137 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h19630 : (¬ p2005) ∨ p2027 ∨ p2287 ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h19630 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47889 (p1988 p2027 p2545 p2579 p3016 p3276 p3355 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19633 : (¬ p1988) ∨ p2027 ∨ p2545 ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p3355))
    : (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3276) ∨ (¬ p3355) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1988 := h2148;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h19633 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47891 (p1984 p2027 p2633 p3554 p3555 p3570 p4129 p4442 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19635 : (¬ p1984) ∨ p2027 ∨ p2633 ∨ (¬ p3554) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4129) ∨ (¬ p4442))
    : (¬ p3554) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4129) ∨ (¬ p4442) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3554 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4442 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1984 := h2144;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2633) := h40879;
    (Or.elim h19635 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47892 (p2022 p2027 p3146 p3544 p3578 p4075 p4261 p4372 : Prop)
    (h2182 : p2022)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h19636 : (¬ p2022) ∨ p2027 ∨ (¬ p3146) ∨ (¬ p3544) ∨ p3578 ∨ (¬ p4075) ∨ (¬ p4261) ∨ (¬ p4372))
    : (¬ p3146) ∨ (¬ p3544) ∨ (¬ p4075) ∨ (¬ p4261) ∨ (¬ p4372) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3544 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4075 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4372 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2022 := h2182;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h19636 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47894 (p1997 p2027 p2088 p2534 p2633 p2850 p3486 p3555 p3570 p3874 p5239 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19638 : (¬ p1997) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2534) ∨ p2633 ∨ (¬ p2850) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3874) ∨ (¬ p5239))
    : (¬ p2088) ∨ (¬ p2534) ∨ (¬ p2850) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p3874) ∨ (¬ p5239) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5239 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p1997 := h2157;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2633) := h40879;
    (Or.elim h19638 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u10 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step47895 (p1975 p2027 p2233 p2470 p2553 p3422 p3874 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19639 : (¬ p1975) ∨ p2027 ∨ p2233 ∨ (¬ p2470) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3874))
    : (¬ p2470) ∨ (¬ p2553) ∨ (¬ p3422) ∨ (¬ p3874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1975 := h2135;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19639 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47896 (p1988 p2027 p2088 p2103 p2842 p3266 p3537 p3585 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40885 : (¬ p2842))
    (h19640 : (¬ p1988) ∨ p2027 ∨ (¬ p2088) ∨ (¬ p2103) ∨ p2842 ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3585))
    : (¬ p2088) ∨ (¬ p2103) ∨ (¬ p3266) ∨ (¬ p3537) ∨ (¬ p3585) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2103 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2842) := h40885;
    (Or.elim h19640 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47898 (p1991 p2027 p2633 p2996 p3292 p3553 p3842 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19642 : (¬ p1991) ∨ p2027 ∨ p2633 ∨ (¬ p2996) ∨ (¬ p3292) ∨ (¬ p3553) ∨ (¬ p3842))
    : (¬ p2996) ∨ (¬ p3292) ∨ (¬ p3553) ∨ (¬ p3842) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2996 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19642 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47899 (p1990 p2027 p2459 p2563 p2633 p3692 p3880 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19643 : (¬ p1990) ∨ p2027 ∨ (¬ p2459) ∨ (¬ p2563) ∨ p2633 ∨ (¬ p3692) ∨ (¬ p3880))
    : (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19643 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47901 (p2005 p2027 p2169 p2363 p2534 p3422 p3874 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40866 : (¬ p2169))
    (h19645 : (¬ p2005) ∨ p2027 ∨ p2169 ∨ (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3874))
    : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p3422) ∨ (¬ p3874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2169) := h40866;
    (Or.elim h19645 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47902 (p1997 p2027 p2850 p2881 p2938 p3644 p3876 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19646 : (¬ p1997) ∨ p2027 ∨ (¬ p2850) ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3644) ∨ (¬ p3876))
    : (¬ p2850) ∨ (¬ p2881) ∨ (¬ p3644) ∨ (¬ p3876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h19646 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47903 (p1982 p2459 p3498 p4438 : Prop)
    (h2142 : p1982)
    (h40899 : (¬ p3498))
    (h19647 : (¬ p1982) ∨ (¬ p2459) ∨ p3498 ∨ p4438)
    : (¬ p2459) ∨ p4438 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4438) := (fun h => hn (Or.inr h));
    let u2 : p1982 := h2142;
    let u3 : (¬ p3498) := h40899;
    (Or.elim h19647 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47904 (p1979 p2027 p2881 p2938 p3136 p3543 p3548 p3572 p4155 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19648 : (¬ p1979) ∨ p2027 ∨ (¬ p2881) ∨ p2938 ∨ (¬ p3136) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4155))
    : (¬ p2881) ∨ (¬ p3136) ∨ (¬ p3543) ∨ (¬ p3548) ∨ (¬ p3572) ∨ (¬ p4155) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1979 := h2139;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2938) := h40888;
    (Or.elim h19648 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47906 (p1982 p2027 p2459 p2688 p3027 p3171 p3998 p4044 p5558 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19651 : (¬ p1982) ∨ p2027 ∨ (¬ p2459) ∨ p2688 ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4044) ∨ (¬ p5558))
    : (¬ p2459) ∨ (¬ p3027) ∨ (¬ p3171) ∨ (¬ p3998) ∨ (¬ p4044) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1982 := h2142;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2688) := h40880;
    (Or.elim h19651 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47908 (p2010 p2027 p2470 p2656 p2688 p2727 p3201 p3874 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19653 : (¬ p2010) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p3201) ∨ (¬ p3874))
    : (¬ p2470) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3201) ∨ (¬ p3874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19653 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47911 (p1982 p2027 p2352 p2363 p2598 p2611 p3422 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19656 : (¬ p1982) ∨ p2027 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2598) ∨ p2611 ∨ (¬ p3422))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2598) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2611) := h40877;
    (Or.elim h19656 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u6 q5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47913 (p1991 p2952 p3474 p5053 : Prop)
    (h2151 : p1991)
    (h40898 : (¬ p3474))
    (h19658 : (¬ p1991) ∨ (¬ p2952) ∨ p3474 ∨ p5053)
    : (¬ p2952) ∨ p5053 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5053) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p3474) := h40898;
    (Or.elim h19658 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47914 (p1982 p2027 p2177 p2307 p2459 p2545 p2578 p3016 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19659 : (¬ p1982) ∨ p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ p2545 ∨ (¬ p2578) ∨ (¬ p3016))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2578) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19659 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47915 (p1984 p2027 p2187 p2247 p2765 p3324 p4154 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19660 : (¬ p1984) ∨ p2027 ∨ (¬ p2187) ∨ (¬ p2247) ∨ p2765 ∨ (¬ p3324) ∨ (¬ p4154))
    : (¬ p2187) ∨ (¬ p2247) ∨ (¬ p3324) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19660 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47917 (p1996 p2287 p2295 p4570 : Prop)
    (h2156 : p1996)
    (h40869 : (¬ p2287))
    (h19662 : (¬ p1996) ∨ p2287 ∨ (¬ p2295) ∨ p4570)
    : (¬ p2295) ∨ p4570 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4570) := (fun h => hn (Or.inr h));
    let u2 : p1996 := h2156;
    let u3 : (¬ p2287) := h40869;
    (Or.elim h19662 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47918 (p1997 p2027 p2850 p3043 p3680 p4264 p4321 p5160 p5487 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40893 : (¬ p3043))
    (h19663 : (¬ p1997) ∨ p2027 ∨ (¬ p2850) ∨ p3043 ∨ (¬ p3680) ∨ (¬ p4264) ∨ (¬ p4321) ∨ (¬ p5160) ∨ (¬ p5487))
    : (¬ p2850) ∨ (¬ p3680) ∨ (¬ p4264) ∨ (¬ p4321) ∨ (¬ p5160) ∨ (¬ p5487) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1997 := h2157;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p3043) := h40893;
    (Or.elim h19663 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47920 (p1998 p2027 p2470 p2528 p2914 p3540 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h19666 : (¬ p1998) ∨ p2027 ∨ (¬ p2470) ∨ (¬ p2528) ∨ p2914 ∨ (¬ p3540) ∨ (¬ p4348))
    : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p3540) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2914) := h40887;
    (Or.elim h19666 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47921 (p1982 p2027 p2373 p2873 p2891 p3146 p3556 p4031 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h19667 : (¬ p1982) ∨ p2027 ∨ (¬ p2373) ∨ p2873 ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3556) ∨ (¬ p4031))
    : (¬ p2373) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3556) ∨ (¬ p4031) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1982 := h2142;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2873) := h40886;
    (Or.elim h19667 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47922 (p1982 p2027 p2230 p2233 p2528 p3641 p3684 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19669 : (¬ p1982) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684))
    : (¬ p2230) ∨ (¬ p2528) ∨ (¬ p3641) ∨ (¬ p3684) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3684 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19669 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47924 (p1988 p2027 p2417 p2656 p2688 p2727 p2761 p3389 : Prop)
    (h2148 : p1988)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19671 : (¬ p1988) ∨ p2027 ∨ (¬ p2417) ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2761) ∨ (¬ p3389))
    : (¬ p2417) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2761) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1988 := h2148;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19671 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47925 (p2005 p2027 p3146 p3578 p4118 p4196 p4228 p5514 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h19672 : (¬ p2005) ∨ p2027 ∨ (¬ p3146) ∨ p3578 ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4228) ∨ (¬ p5514))
    : (¬ p3146) ∨ (¬ p4118) ∨ (¬ p4196) ∨ (¬ p4228) ∨ (¬ p5514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h19672 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47926 (p1997 p2027 p2534 p2545 p2850 p3256 p3874 p4121 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19673 : (¬ p1997) ∨ p2027 ∨ (¬ p2534) ∨ p2545 ∨ (¬ p2850) ∨ (¬ p3256) ∨ (¬ p3874) ∨ (¬ p4121))
    : (¬ p2534) ∨ (¬ p2850) ∨ (¬ p3256) ∨ (¬ p3874) ∨ (¬ p4121) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2534 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19673 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47927 (p1997 p2027 p2764 p2870 p4235 p4322 p4385 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19674 : (¬ p1997) ∨ p2027 ∨ p2764 ∨ (¬ p2870) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4385))
    : (¬ p2870) ∨ (¬ p4235) ∨ (¬ p4322) ∨ (¬ p4385) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1997 := h2157;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19674 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47930 (p1997 p2027 p2481 p2850 p3146 p3578 p3857 p3874 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40900 : (¬ p3578))
    (h19677 : (¬ p1997) ∨ p2027 ∨ (¬ p2481) ∨ (¬ p2850) ∨ (¬ p3146) ∨ p3578 ∨ (¬ p3857) ∨ (¬ p3874))
    : (¬ p2481) ∨ (¬ p2850) ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3874) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3578) := h40900;
    (Or.elim h19677 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u7 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47932 (p1999 p2027 p2230 p2611 p3125 p3362 p3660 p3888 p4393 : Prop)
    (h2159 : p1999)
    (h40810 : (¬ p2027))
    (h40877 : (¬ p2611))
    (h19680 : (¬ p1999) ∨ p2027 ∨ (¬ p2230) ∨ p2611 ∨ (¬ p3125) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4393))
    : (¬ p2230) ∨ (¬ p3125) ∨ (¬ p3362) ∨ (¬ p3660) ∨ (¬ p3888) ∨ (¬ p4393) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3888 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1999 := h2159;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2611) := h40877;
    (Or.elim h19680 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u8 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47933 (p1997 p2027 p2573 p2656 p2688 p2727 p2850 p3584 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h19681 : (¬ p1997) ∨ p2027 ∨ (¬ p2573) ∨ (¬ p2656) ∨ p2688 ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p3584))
    : (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2850) ∨ (¬ p3584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2688) := h40880;
    (Or.elim h19681 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47935 (p2005 p2027 p2509 p2534 p2657 p2766 p3361 p3422 p3487 p3686 p4781 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19683 : (¬ p2005) ∨ p2027 ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2657) ∨ p2766 ∨ (¬ p3361) ∨ (¬ p3422) ∨ (¬ p3487) ∨ (¬ p3686) ∨ (¬ p4781))
    : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3361) ∨ (¬ p3422) ∨ (¬ p3487) ∨ (¬ p3686) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2534 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2005 := h2165;
    let u9 : (¬ p2027) := h40810;
    let u10 : (¬ p2766) := h40884;
    (Or.elim h19683 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u9 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (u10 q5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (False.elim (r9 u7)))))))))))))))))))))))

theorem step47938 (p1984 p2027 p2247 p2764 p2996 p3947 p4381 : Prop)
    (h2144 : p1984)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19687 : (¬ p1984) ∨ p2027 ∨ (¬ p2247) ∨ p2764 ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381))
    : (¬ p2247) ∨ (¬ p2996) ∨ (¬ p3947) ∨ (¬ p4381) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1984 := h2144;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19687 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47940 (p1983 p2027 p2210 p2409 p2891 p3246 p3452 : Prop)
    (h2143 : p1983)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h19689 : (¬ p1983) ∨ p2027 ∨ (¬ p2210) ∨ p2409 ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3452))
    : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1983 := h2143;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h19689 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47941 (p2005 p2027 p2114 p3063 p3093 p3954 p3956 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19690 : (¬ p2005) ∨ p2027 ∨ p2114 ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3956))
    : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3954) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h19690 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47942 (p1975 p2027 p2202 p2299 p2911 p3238 p3389 p3519 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h19691 : (¬ p1975) ∨ p2027 ∨ p2202 ∨ (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519))
    : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h19691 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47943 (p1998 p2027 p2177 p2409 p3093 p3309 p3452 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h19692 : (¬ p1998) ∨ p2027 ∨ (¬ p2177) ∨ p2409 ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452))
    : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h19692 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47944 (p1991 p2027 p2765 p3005 p3172 p3952 p4315 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19693 : (¬ p1991) ∨ p2027 ∨ p2765 ∨ (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3952) ∨ (¬ p4315))
    : (¬ p3005) ∨ (¬ p3172) ∨ (¬ p3952) ∨ (¬ p4315) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h19693 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47945 (p1978 p2027 p2766 p2901 p3497 p3556 p3692 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19694 : (¬ p1978) ∨ p2027 ∨ p2766 ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3692))
    : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3692) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h19694 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47946 (p1998 p2027 p2409 p3073 p3449 p3452 p4348 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40874 : (¬ p2409))
    (h19695 : (¬ p1998) ∨ p2027 ∨ p2409 ∨ (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4348))
    : (¬ p3073) ∨ (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2409) := h40874;
    (Or.elim h19695 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47949 (p1997 p2027 p2573 p2766 p2850 p2952 p3362 p3497 p3564 p3692 p3917 p4789 p5220 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h19698 : (¬ p1997) ∨ p2027 ∨ (¬ p2573) ∨ p2766 ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3917) ∨ (¬ p4789) ∨ (¬ p5220))
    : (¬ p2573) ∨ (¬ p2850) ∨ (¬ p2952) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p3917) ∨ (¬ p4789) ∨ (¬ p5220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p1997 := h2157;
    let u11 : (¬ p2027) := h40810;
    let u12 : (¬ p2766) := h40884;
    (Or.elim h19698 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u11 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u12 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u6))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u7))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u8))) (fun r11 => (False.elim (r11 u9)))))))))))))))))))))))))))

theorem step47950 (p2007 p2027 p2573 p2964 p3346 p3584 p3641 : Prop)
    (h2167 : p2007)
    (h40810 : (¬ p2027))
    (h40889 : (¬ p2964))
    (h19699 : (¬ p2007) ∨ p2027 ∨ (¬ p2573) ∨ p2964 ∨ (¬ p3346) ∨ (¬ p3584) ∨ (¬ p3641))
    : (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3584) ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2007 := h2167;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2964) := h40889;
    (Or.elim h19699 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47951 (p1997 p2027 p2114 p2850 p3449 p3874 p3954 p4687 : Prop)
    (h2157 : p1997)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19700 : (¬ p1997) ∨ p2027 ∨ p2114 ∨ (¬ p2850) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687))
    : (¬ p2850) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1997 := h2157;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19700 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47953 (p1981 p2027 p2355 p2819 p3822 p3931 p4260 : Prop)
    (h2141 : p1981)
    (h40810 : (¬ p2027))
    (h40872 : (¬ p2355))
    (h19702 : (¬ p1981) ∨ p2027 ∨ p2355 ∨ (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3931) ∨ (¬ p4260))
    : (¬ p2819) ∨ (¬ p3822) ∨ (¬ p3931) ∨ (¬ p4260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1981 := h2141;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2355) := h40872;
    (Or.elim h19702 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47955 (p2022 p2027 p2765 p3156 p3952 p3961 p3969 p5590 : Prop)
    (h2182 : p2022)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h19704 : (¬ p2022) ∨ p2027 ∨ p2765 ∨ (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3961) ∨ (¬ p3969) ∨ (¬ p5590))
    : (¬ p3156) ∨ (¬ p3952) ∨ (¬ p3961) ∨ (¬ p3969) ∨ (¬ p5590) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3961 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2022 := h2182;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2765) := h40883;
    (Or.elim h19704 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47957 (p2005 p2027 p3063 p3093 p3623 p3956 p4366 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40903 : (¬ p3623))
    (h19706 : (¬ p2005) ∨ p2027 ∨ (¬ p3063) ∨ (¬ p3093) ∨ p3623 ∨ (¬ p3956) ∨ (¬ p4366))
    : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3956) ∨ (¬ p4366) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3623) := h40903;
    (Or.elim h19706 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47958 (p1978 p2027 p2901 p2997 p3097 p3556 p3952 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19707 : (¬ p1978) ∨ p2027 ∨ (¬ p2901) ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3556) ∨ (¬ p3952))
    : (¬ p2901) ∨ (¬ p3097) ∨ (¬ p3556) ∨ (¬ p3952) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19707 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47959 (p1975 p2027 p2264 p2299 p2545 p2797 p2810 p4156 : Prop)
    (h2135 : p1975)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19708 : (¬ p1975) ∨ p2027 ∨ (¬ p2264) ∨ (¬ p2299) ∨ p2545 ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4156))
    : (¬ p2264) ∨ (¬ p2299) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p4156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1975 := h2135;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2545) := h40876;
    (Or.elim h19708 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47960 (p2004 p2409 p2922 p2930 : Prop)
    (h2164 : p2004)
    (h40874 : (¬ p2409))
    (h19709 : (¬ p2004) ∨ p2409 ∨ (¬ p2922) ∨ p2930)
    : (¬ p2922) ∨ p2930 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2930) := (fun h => hn (Or.inr h));
    let u2 : p2004 := h2164;
    let u3 : (¬ p2409) := h40874;
    (Or.elim h19709 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47962 (p2005 p2027 p2295 p2545 p2588 p2797 p2810 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40876 : (¬ p2545))
    (h19711 : (¬ p2005) ∨ p2027 ∨ (¬ p2295) ∨ p2545 ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2810))
    : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p2810) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2005 := h2165;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2545) := h40876;
    (Or.elim h19711 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47966 (p1976 p2027 p2764 p2952 p3136 p4035 p4040 p4236 p4322 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19715 : (¬ p1976) ∨ p2027 ∨ p2764 ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p4040) ∨ (¬ p4236) ∨ (¬ p4322))
    : (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4035) ∨ (¬ p4040) ∨ (¬ p4236) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4035 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4040 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1976 := h2136;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2764) := h40882;
    (Or.elim h19715 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u8 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step47967 (p1976 p2027 p2104 p3146 p3982 p4340 p5568 : Prop)
    (h2136 : p1976)
    (h40810 : (¬ p2027))
    (h40909 : (¬ p3982))
    (h19716 : (¬ p1976) ∨ p2027 ∨ (¬ p2104) ∨ (¬ p3146) ∨ p3982 ∨ (¬ p4340) ∨ (¬ p5568))
    : (¬ p2104) ∨ (¬ p3146) ∨ (¬ p4340) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1976 := h2136;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p3982) := h40909;
    (Or.elim h19716 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47968 (p2010 p2027 p2287 p2499 p2922 p3323 p4137 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40869 : (¬ p2287))
    (h19718 : (¬ p2010) ∨ p2027 ∨ p2287 ∨ (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3323) ∨ (¬ p4137))
    : (¬ p2499) ∨ (¬ p2922) ∨ (¬ p3323) ∨ (¬ p4137) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2010 := h2170;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2287) := h40869;
    (Or.elim h19718 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47969 (p1998 p2027 p2114 p2210 p2881 p2891 p3954 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19719 : (¬ p1998) ∨ p2027 ∨ p2114 ∨ (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3954))
    : (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1998 := h2158;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h19719 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47971 (p1987 p2027 p2737 p2764 p4242 p4340 p4444 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19721 : (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ p2764 ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4444))
    : (¬ p2737) ∨ (¬ p4242) ∨ (¬ p4340) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4242 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1987 := h2147;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19721 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47972 (p2005 p2233 p2470 p4595 : Prop)
    (h2165 : p2005)
    (h40868 : (¬ p2233))
    (h19722 : (¬ p2005) ∨ p2233 ∨ (¬ p2470) ∨ p4595)
    : (¬ p2470) ∨ p4595 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4595) := (fun h => hn (Or.inr h));
    let u2 : p2005 := h2165;
    let u3 : (¬ p2233) := h40868;
    (Or.elim h19722 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47976 (p1978 p2027 p2284 p2764 p3646 p4208 p4322 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h19726 : (¬ p1978) ∨ p2027 ∨ (¬ p2284) ∨ p2764 ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p4322))
    : (¬ p2284) ∨ (¬ p3646) ∨ (¬ p4208) ∨ (¬ p4322) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h19726 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47979 (p1982 p2027 p2114 p2166 p2210 p3146 p3954 : Prop)
    (h2142 : p1982)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19730 : (¬ p1982) ∨ p2027 ∨ p2114 ∨ (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3954))
    : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1982 := h2142;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2114) := h40864;
    (Or.elim h19730 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47980 (p2005 p2027 p2114 p3422 p3449 p3874 p3954 p4687 : Prop)
    (h2165 : p2005)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19731 : (¬ p2005) ∨ p2027 ∨ p2114 ∨ (¬ p3422) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687))
    : (¬ p3422) ∨ (¬ p3449) ∨ (¬ p3874) ∨ (¬ p3954) ∨ (¬ p4687) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4687 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2005 := h2165;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19731 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47981 (p2010 p2027 p2114 p2504 p3093 p3201 p3584 p3954 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40864 : (¬ p2114))
    (h19732 : (¬ p2010) ∨ p2027 ∨ p2114 ∨ (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3954))
    : (¬ p2504) ∨ (¬ p3093) ∨ (¬ p3201) ∨ (¬ p3584) ∨ (¬ p3954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2504 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2114) := h40864;
    (Or.elim h19732 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step47982 (p1986 p2027 p2579 p2588 p2997 p3355 p5160 : Prop)
    (h2146 : p1986)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19733 : (¬ p1986) ∨ p2027 ∨ (¬ p2579) ∨ (¬ p2588) ∨ p2997 ∨ (¬ p3355) ∨ (¬ p5160))
    : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3355) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2579 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1986 := h2146;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19733 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47986 (p1985 p2027 p2230 p2233 p2373 p2870 p3694 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h19737 : (¬ p1985) ∨ p2027 ∨ (¬ p2230) ∨ p2233 ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p3694))
    : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p2870) ∨ (¬ p3694) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2233) := h40868;
    (Or.elim h19737 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47988 (p1990 p2027 p2299 p2633 p3323 p3568 p3744 : Prop)
    (h2150 : p1990)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19740 : (¬ p1990) ∨ p2027 ∨ (¬ p2299) ∨ p2633 ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3744))
    : (¬ p2299) ∨ (¬ p3323) ∨ (¬ p3568) ∨ (¬ p3744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1990 := h2150;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19740 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47990 (p1978 p2027 p2997 p3097 p3115 p3952 p4032 : Prop)
    (h2138 : p1978)
    (h40810 : (¬ p2027))
    (h40890 : (¬ p2997))
    (h19742 : (¬ p1978) ∨ p2027 ∨ p2997 ∨ (¬ p3097) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4032))
    : (¬ p3097) ∨ (¬ p3115) ∨ (¬ p3952) ∨ (¬ p4032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1978 := h2138;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2997) := h40890;
    (Or.elim h19742 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47992 (p1991 p2027 p2633 p3246 p3414 p3570 p3947 : Prop)
    (h2151 : p1991)
    (h40810 : (¬ p2027))
    (h40879 : (¬ p2633))
    (h19744 : (¬ p1991) ∨ p2027 ∨ p2633 ∨ (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3570) ∨ (¬ p3947))
    : (¬ p3246) ∨ (¬ p3414) ∨ (¬ p3570) ∨ (¬ p3947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1991 := h2151;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2633) := h40879;
    (Or.elim h19744 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47993 (p2007 p2388 p3156 p4158 : Prop)
    (h2167 : p2007)
    (h40873 : (¬ p2388))
    (h19745 : (¬ p2007) ∨ p2388 ∨ (¬ p3156) ∨ p4158)
    : (¬ p3156) ∨ p4158 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4158) := (fun h => hn (Or.inr h));
    let u2 : p2007 := h2167;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h19745 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47994 (p2003 p2027 p2284 p2938 p3125 p3946 p4320 : Prop)
    (h2163 : p2003)
    (h40810 : (¬ p2027))
    (h40888 : (¬ p2938))
    (h19746 : (¬ p2003) ∨ p2027 ∨ (¬ p2284) ∨ p2938 ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4320))
    : (¬ p2284) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2003 := h2163;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2938) := h40888;
    (Or.elim h19746 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step47995 (p2027 p2177 p2295 p3570 p4204 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h19749 : p2027 ∨ (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4560))
    : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19749 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step47996 (p1984 p2247 p2255 p2323 : Prop)
    (h2144 : p1984)
    (h40870 : (¬ p2323))
    (h19754 : (¬ p1984) ∨ (¬ p2247) ∨ p2255 ∨ p2323)
    : (¬ p2247) ∨ p2255 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2255) := (fun h => hn (Or.inr h));
    let u2 : p1984 := h2144;
    let u3 : (¬ p2323) := h40870;
    (Or.elim h19754 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step47997 (p2027 p2589 p2662 p2745 p2850 p3475 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h19755 : p2027 ∨ (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p4111))
    : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2745) ∨ (¬ p2850) ∨ (¬ p3475) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19755 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step47998 (p1991 p2233 p2657 p2665 : Prop)
    (h2151 : p1991)
    (h40868 : (¬ p2233))
    (h19759 : (¬ p1991) ∨ p2233 ∨ (¬ p2657) ∨ p2665)
    : (¬ p2657) ∨ p2665 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2665) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p2233) := h40868;
    (Or.elim h19759 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step47999 (p2003 p2313 p2321 p3360 : Prop)
    (h2163 : p2003)
    (h40895 : (¬ p3360))
    (h19764 : (¬ p2003) ∨ (¬ p2313) ∨ p2321 ∨ p3360)
    : (¬ p2313) ∨ p2321 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2321) := (fun h => hn (Or.inr h));
    let u2 : p2003 := h2163;
    let u3 : (¬ p3360) := h40895;
    (Or.elim h19764 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step48000 (p2027 p2104 p2132 p3156 p4740 p4906 : Prop)
    (h40810 : (¬ p2027))
    (h19766 : p2027 ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3156) ∨ (¬ p4740) ∨ (¬ p4906))
    : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p3156) ∨ (¬ p4740) ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19766 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48001 (p2027 p3379 p3688 p3954 p4030 p5221 : Prop)
    (h40810 : (¬ p2027))
    (h19771 : p2027 ∨ (¬ p3379) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p5221))
    : (¬ p3379) ∨ (¬ p3688) ∨ (¬ p3954) ∨ (¬ p4030) ∨ (¬ p5221) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5221 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19771 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48003 (p2027 p2312 p2341 p2501 p2553 p3548 p4105 : Prop)
    (h40810 : (¬ p2027))
    (h19778 : p2027 ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p4105))
    : (¬ p2312) ∨ (¬ p2341) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3548) ∨ (¬ p4105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2312 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19778 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48006 (p2027 p2341 p3425 p3548 p3819 p4794 : Prop)
    (h40810 : (¬ p2027))
    (h19794 : p2027 ∨ (¬ p2341) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p4794))
    : (¬ p2341) ∨ (¬ p3425) ∨ (¬ p3548) ∨ (¬ p3819) ∨ (¬ p4794) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19794 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48007 (p2027 p2707 p3583 p4235 p4344 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h19796 : p2027 ∨ (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4885))
    : (¬ p2707) ∨ (¬ p3583) ∨ (¬ p4235) ∨ (¬ p4344) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19796 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48008 (p2027 p2132 p2810 p3365 p4704 p5051 : Prop)
    (h40810 : (¬ p2027))
    (h19798 : p2027 ∨ (¬ p2132) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4704) ∨ (¬ p5051))
    : (¬ p2132) ∨ (¬ p2810) ∨ (¬ p3365) ∨ (¬ p4704) ∨ (¬ p5051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19798 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48009 (p2027 p2657 p2743 p3367 p3683 p4787 : Prop)
    (h40810 : (¬ p2027))
    (h19799 : p2027 ∨ (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4787))
    : (¬ p2657) ∨ (¬ p2743) ∨ (¬ p3367) ∨ (¬ p3683) ∨ (¬ p4787) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3683 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19799 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48012 (p2027 p2230 p2563 p3054 p3758 p4730 : Prop)
    (h40810 : (¬ p2027))
    (h19809 : p2027 ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p4730))
    : (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3054) ∨ (¬ p3758) ∨ (¬ p4730) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3054 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3758 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4730 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19809 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48013 (p1991 p2247 p2254 p2688 : Prop)
    (h2151 : p1991)
    (h40880 : (¬ p2688))
    (h19812 : (¬ p1991) ∨ (¬ p2247) ∨ p2254 ∨ p2688)
    : (¬ p2247) ∨ p2254 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2254) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p2688) := h40880;
    (Or.elim h19812 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step48014 (p2027 p2341 p2737 p3548 p3577 p4400 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h19816 : p2027 ∨ (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3548) ∨ (¬ p3577) ∨ (¬ p4400) ∨ (¬ p4778))
    : (¬ p2341) ∨ (¬ p2737) ∨ (¬ p3548) ∨ (¬ p3577) ∨ (¬ p4400) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19816 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48015 (p2027 p2156 p2958 p3414 p3952 p4917 : Prop)
    (h40810 : (¬ p2027))
    (h19818 : p2027 ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4917))
    : (¬ p2156) ∨ (¬ p2958) ∨ (¬ p3414) ∨ (¬ p3952) ∨ (¬ p4917) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4917 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19818 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48017 (p2027 p2630 p2707 p2741 p4111 p4782 : Prop)
    (h40810 : (¬ p2027))
    (h19828 : p2027 ∨ (¬ p2630) ∨ (¬ p2707) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4782))
    : (¬ p2630) ∨ (¬ p2707) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4782) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4782 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19828 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48018 (p2027 p2122 p2745 p3568 p4154 p4426 : Prop)
    (h40810 : (¬ p2027))
    (h19831 : p2027 ∨ (¬ p2122) ∨ (¬ p2745) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4426))
    : (¬ p2122) ∨ (¬ p2745) ∨ (¬ p3568) ∨ (¬ p4154) ∨ (¬ p4426) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4426 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19831 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48019 (p2003 p2233 p2573 p2581 : Prop)
    (h2163 : p2003)
    (h40868 : (¬ p2233))
    (h19840 : (¬ p2003) ∨ p2233 ∨ (¬ p2573) ∨ p2581)
    : (¬ p2573) ∨ p2581 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2581) := (fun h => hn (Or.inr h));
    let u2 : p2003 := h2163;
    let u3 : (¬ p2233) := h40868;
    (Or.elim h19840 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48020 (p2027 p2230 p2737 p3238 p3759 p4257 p4749 : Prop)
    (h40810 : (¬ p2027))
    (h19845 : p2027 ∨ (¬ p2230) ∨ (¬ p2737) ∨ (¬ p3238) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749))
    : (¬ p2230) ∨ (¬ p2737) ∨ (¬ p3238) ∨ (¬ p3759) ∨ (¬ p4257) ∨ (¬ p4749) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19845 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48022 (p2027 p3461 p3690 p4187 p4381 p4556 : Prop)
    (h40810 : (¬ p2027))
    (h19847 : p2027 ∨ (¬ p3461) ∨ (¬ p3690) ∨ (¬ p4187) ∨ (¬ p4381) ∨ (¬ p4556))
    : (¬ p3461) ∨ (¬ p3690) ∨ (¬ p4187) ∨ (¬ p4381) ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19847 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48023 (p2027 p3355 p3540 p3947 p4327 p4451 : Prop)
    (h40810 : (¬ p2027))
    (h19851 : p2027 ∨ (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4451))
    : (¬ p3355) ∨ (¬ p3540) ∨ (¬ p3947) ∨ (¬ p4327) ∨ (¬ p4451) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19851 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48024 (p2027 p2881 p2891 p4363 p4382 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h19856 : p2027 ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4666))
    : (¬ p2881) ∨ (¬ p2891) ∨ (¬ p4363) ∨ (¬ p4382) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19856 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48025 (p2027 p3707 p4322 p4385 p4878 p4942 : Prop)
    (h40810 : (¬ p2027))
    (h19864 : p2027 ∨ (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4878) ∨ (¬ p4942))
    : (¬ p3707) ∨ (¬ p4322) ∨ (¬ p4385) ∨ (¬ p4878) ∨ (¬ p4942) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4942 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19864 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48027 (p2027 p2589 p2608 p2737 p3005 p3989 p4110 p4771 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h19874 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4771) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p2737) ∨ (¬ p3005) ∨ (¬ p3989) ∨ (¬ p4110) ∨ (¬ p4771) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4771 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h19874 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48028 (p2027 p2341 p2459 p2952 p3266 p3952 p4393 p4850 p5248 : Prop)
    (h40810 : (¬ p2027))
    (h19875 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h19875 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48029 (p2027 p2341 p2459 p2952 p3266 p3952 p4393 p4850 p5254 : Prop)
    (h40810 : (¬ p2027))
    (h19876 : p2027 ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5254))
    : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h19876 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48030 (p2027 p3461 p3990 p4348 p4444 p4503 : Prop)
    (h40810 : (¬ p2027))
    (h19882 : p2027 ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4503))
    : (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19882 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48031 (p2027 p2476 p3355 p4261 p4685 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h19885 : p2027 ∨ (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4261) ∨ (¬ p4685) ∨ (¬ p4695))
    : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4261) ∨ (¬ p4685) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2476 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19885 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48032 (p2027 p2972 p3371 p3585 p4385 p4884 : Prop)
    (h40810 : (¬ p2027))
    (h19890 : p2027 ∨ (¬ p2972) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p4385) ∨ (¬ p4884))
    : (¬ p2972) ∨ (¬ p3371) ∨ (¬ p3585) ∨ (¬ p4385) ∨ (¬ p4884) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4385 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4884 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19890 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48034 (p2027 p2156 p2850 p3096 p3370 p3584 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h19904 : p2027 ∨ (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3370) ∨ (¬ p3584) ∨ (¬ p4632))
    : (¬ p2156) ∨ (¬ p2850) ∨ (¬ p3096) ∨ (¬ p3370) ∨ (¬ p3584) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19904 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48035 (p1994 p2027 p2873 p2922 p3379 p3555 p3742 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40886 : (¬ p2873))
    (h19906 : (¬ p1994) ∨ p2027 ∨ p2873 ∨ (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3742))
    : (¬ p2922) ∨ (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3742) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2873) := h40886;
    (Or.elim h19906 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u6 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step48036 (p1977 p2241 p2248 p2323 : Prop)
    (h2137 : p1977)
    (h40870 : (¬ p2323))
    (h19909 : (¬ p1977) ∨ (¬ p2241) ∨ p2248 ∨ p2323)
    : (¬ p2241) ∨ p2248 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2248) := (fun h => hn (Or.inr h));
    let u2 : p1977 := h2137;
    let u3 : (¬ p2323) := h40870;
    (Or.elim h19909 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step48038 (p2027 p2187 p2307 p2387 p3549 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h19935 : p2027 ∨ (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3549) ∨ (¬ p4514))
    : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p3549) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19935 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48040 (p2027 p2717 p2810 p3553 p4652 p4781 : Prop)
    (h40810 : (¬ p2027))
    (h19952 : p2027 ∨ (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3553) ∨ (¬ p4652) ∨ (¬ p4781))
    : (¬ p2717) ∨ (¬ p2810) ∨ (¬ p3553) ∨ (¬ p4652) ∨ (¬ p4781) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19952 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48041 (p2027 p2810 p3005 p3238 p4346 p4607 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h19956 : p2027 ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4811))
    : (¬ p2810) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p4346) ∨ (¬ p4607) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2810 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19956 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48042 (p2027 p2509 p2810 p3005 p4346 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h19957 : p2027 ∨ (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346) ∨ (¬ p4811))
    : (¬ p2509) ∨ (¬ p2810) ∨ (¬ p3005) ∨ (¬ p4346) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19957 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48043 (p2027 p2230 p2437 p3238 p3540 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h19960 : p2027 ∨ (¬ p2230) ∨ (¬ p2437) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4811))
    : (¬ p2230) ∨ (¬ p2437) ∨ (¬ p3238) ∨ (¬ p3540) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3540 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19960 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48044 (p2027 p2911 p3941 p4278 p4445 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h19961 : p2027 ∨ (¬ p2911) ∨ (¬ p3941) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p5122))
    : (¬ p2911) ∨ (¬ p3941) ∨ (¬ p4278) ∨ (¬ p4445) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3941 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4278 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19961 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48046 (p2027 p2299 p3516 p3527 p3577 p3817 p4477 : Prop)
    (h40810 : (¬ p2027))
    (h19964 : p2027 ∨ (¬ p2299) ∨ (¬ p3516) ∨ (¬ p3527) ∨ (¬ p3577) ∨ (¬ p3817) ∨ (¬ p4477))
    : (¬ p2299) ∨ (¬ p3516) ∨ (¬ p3527) ∨ (¬ p3577) ∨ (¬ p3817) ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3817 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h19964 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48048 (p2027 p2299 p3527 p4435 p4452 p5472 : Prop)
    (h40810 : (¬ p2027))
    (h19967 : p2027 ∨ (¬ p2299) ∨ (¬ p3527) ∨ (¬ p4435) ∨ (¬ p4452) ∨ (¬ p5472))
    : (¬ p2299) ∨ (¬ p3527) ∨ (¬ p4435) ∨ (¬ p4452) ∨ (¬ p5472) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4452 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19967 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48049 (p2027 p2528 p3083 p3453 p4261 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h19970 : p2027 ∨ (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4811))
    : (¬ p2528) ∨ (¬ p3083) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19970 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48053 (p2027 p2819 p2829 p3588 p4405 p4471 : Prop)
    (h40810 : (¬ p2027))
    (h19978 : p2027 ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4405) ∨ (¬ p4471))
    : (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4405) ∨ (¬ p4471) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19978 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48056 (p2027 p2630 p2946 p2963 p4315 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h19987 : p2027 ∨ (¬ p2630) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4315) ∨ (¬ p4972))
    : (¬ p2630) ∨ (¬ p2946) ∨ (¬ p2963) ∨ (¬ p4315) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19987 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48057 (p2027 p2651 p2685 p3414 p4195 p4972 : Prop)
    (h40810 : (¬ p2027))
    (h19988 : p2027 ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p4195) ∨ (¬ p4972))
    : (¬ p2651) ∨ (¬ p2685) ∨ (¬ p3414) ∨ (¬ p4195) ∨ (¬ p4972) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4195 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4972 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19988 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48059 (p2027 p2449 p2807 p3172 p4548 p4668 : Prop)
    (h40810 : (¬ p2027))
    (h19993 : p2027 ∨ (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p4668))
    : (¬ p2449) ∨ (¬ p2807) ∨ (¬ p3172) ∨ (¬ p4548) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h19993 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48064 (p2027 p2177 p3027 p4360 p4548 p4570 : Prop)
    (h40810 : (¬ p2027))
    (h20030 : p2027 ∨ (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570))
    : (¬ p2177) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20030 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48065 (p2027 p2573 p2911 p3551 p4708 p5197 : Prop)
    (h40810 : (¬ p2027))
    (h20033 : p2027 ∨ (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4708) ∨ (¬ p5197))
    : (¬ p2573) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4708) ∨ (¬ p5197) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4708 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20033 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48066 (p2027 p2373 p2387 p2406 p2459 p3379 p4347 p4902 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h20035 : p2027 ∨ (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021))
    : (¬ p2373) ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2459) ∨ (¬ p3379) ∨ (¬ p4347) ∨ (¬ p4902) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20035 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48067 (p1977 p2499 p2507 p3402 p3818 : Prop)
    (h2137 : p1977)
    (h40905 : (¬ p3818))
    (h20036 : (¬ p1977) ∨ (¬ p2499) ∨ p2507 ∨ (¬ p3402) ∨ p3818)
    : (¬ p2499) ∨ p2507 ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2507) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1977 := h2137;
    let u4 : (¬ p3818) := h40905;
    (Or.elim h20036 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (u4 r3)))))))))))

theorem step48070 (p2027 p2751 p2992 p3156 p3694 p4392 : Prop)
    (h40810 : (¬ p2027))
    (h20045 : p2027 ∨ (¬ p2751) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p4392))
    : (¬ p2751) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3694) ∨ (¬ p4392) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4392 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20045 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48071 (p2027 p2737 p2797 p3585 p4343 p4975 : Prop)
    (h40810 : (¬ p2027))
    (h20053 : p2027 ∨ (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975))
    : (¬ p2737) ∨ (¬ p2797) ∨ (¬ p3585) ∨ (¬ p4343) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20053 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48072 (p2027 p2241 p2313 p3309 p4756 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h20057 : p2027 ∨ (¬ p2241) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p4756) ∨ (¬ p5015))
    : (¬ p2241) ∨ (¬ p2313) ∨ (¬ p3309) ∨ (¬ p4756) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20057 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48073 (p2027 p2192 p2241 p2274 p2396 p2750 p3371 p3860 p3950 p4261 : Prop)
    (h40810 : (¬ p2027))
    (h20058 : p2027 ∨ (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261))
    : (¬ p2192) ∨ (¬ p2241) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p3371) ∨ (¬ p3860) ∨ (¬ p3950) ∨ (¬ p4261) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4261 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20058 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48075 (p2027 p2313 p2608 p3309 p4866 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h20061 : p2027 ∨ (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4866) ∨ (¬ p5015))
    : (¬ p2313) ∨ (¬ p2608) ∨ (¬ p3309) ∨ (¬ p4866) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20061 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48076 (p2027 p2313 p2500 p3309 p3379 p5015 : Prop)
    (h40810 : (¬ p2027))
    (h20065 : p2027 ∨ (¬ p2313) ∨ (¬ p2500) ∨ (¬ p3309) ∨ (¬ p3379) ∨ (¬ p5015))
    : (¬ p2313) ∨ (¬ p2500) ∨ (¬ p3309) ∨ (¬ p3379) ∨ (¬ p5015) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2313 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2500 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5015 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20065 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48077 (p2022 p2307 p2315 p2344 : Prop)
    (h2182 : p2022)
    (h40871 : (¬ p2344))
    (h20074 : (¬ p2022) ∨ (¬ p2307) ∨ p2315 ∨ p2344)
    : (¬ p2307) ∨ p2315 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2315) := (fun h => hn (Or.inr h));
    let u2 : p2022 := h2182;
    let u3 : (¬ p2344) := h40871;
    (Or.elim h20074 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step48079 (p2027 p2307 p3549 p3954 p4202 p4512 p5020 p5216 : Prop)
    (h40810 : (¬ p2027))
    (h20078 : p2027 ∨ (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p5020) ∨ (¬ p5216))
    : (¬ p2307) ∨ (¬ p3549) ∨ (¬ p3954) ∨ (¬ p4202) ∨ (¬ p4512) ∨ (¬ p5020) ∨ (¬ p5216) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5216 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h20078 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step48081 (p2027 p2247 p3037 p3399 p3662 p4919 : Prop)
    (h40810 : (¬ p2027))
    (h20090 : p2027 ∨ (¬ p2247) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3662) ∨ (¬ p4919))
    : (¬ p2247) ∨ (¬ p3037) ∨ (¬ p3399) ∨ (¬ p3662) ∨ (¬ p4919) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2247 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20090 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48082 (p2027 p2220 p2284 p3497 p3556 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h20093 : p2027 ∨ (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4555))
    : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3497 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20093 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48083 (p2027 p2563 p3051 p3646 p4320 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h20094 : p2027 ∨ (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4702))
    : (¬ p2563) ∨ (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4320) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20094 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48086 (p2027 p2104 p2132 p2166 p4740 p4960 p5051 : Prop)
    (h40810 : (¬ p2027))
    (h20101 : p2027 ∨ (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p4740) ∨ (¬ p4960) ∨ (¬ p5051))
    : (¬ p2104) ∨ (¬ p2132) ∨ (¬ p2166) ∨ (¬ p4740) ∨ (¬ p4960) ∨ (¬ p5051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2104 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20101 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48088 (p2027 p2088 p2911 p3919 p3960 p4118 p4327 : Prop)
    (h40810 : (¬ p2027))
    (h20105 : p2027 ∨ (¬ p2088) ∨ (¬ p2911) ∨ (¬ p3919) ∨ (¬ p3960) ∨ (¬ p4118) ∨ (¬ p4327))
    : (¬ p2088) ∨ (¬ p2911) ∨ (¬ p3919) ∨ (¬ p3960) ∨ (¬ p4118) ∨ (¬ p4327) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4327 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20105 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48090 (p2027 p2241 p2589 p3189 p3256 p3690 p4235 p4669 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h20117 : p2027 ∨ (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p3189) ∨ (¬ p3256) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20117 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48093 (p2027 p2727 p2946 p3414 p3662 p4650 : Prop)
    (h40810 : (¬ p2027))
    (h20120 : p2027 ∨ (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4650))
    : (¬ p2727) ∨ (¬ p2946) ∨ (¬ p3414) ∨ (¬ p3662) ∨ (¬ p4650) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4650 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20120 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48095 (p2027 p2589 p2608 p3537 p3609 p3690 p4235 p4669 p5193 : Prop)
    (h40810 : (¬ p2027))
    (h20126 : p2027 ∨ (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193))
    : (¬ p2589) ∨ (¬ p2608) ∨ (¬ p3537) ∨ (¬ p3609) ∨ (¬ p3690) ∨ (¬ p4235) ∨ (¬ p4669) ∨ (¬ p5193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3537 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20126 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48097 (p2027 p2528 p3857 p4197 p4235 p4355 p4356 p4555 : Prop)
    (h40810 : (¬ p2027))
    (h20130 : p2027 ∨ (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4235) ∨ (¬ p4355) ∨ (¬ p4356) ∨ (¬ p4555))
    : (¬ p2528) ∨ (¬ p3857) ∨ (¬ p4197) ∨ (¬ p4235) ∨ (¬ p4355) ∨ (¬ p4356) ∨ (¬ p4555) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h20130 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step48099 (p2027 p3654 p3954 p4026 p4870 p5020 : Prop)
    (h40810 : (¬ p2027))
    (h20144 : p2027 ∨ (¬ p3654) ∨ (¬ p3954) ∨ (¬ p4026) ∨ (¬ p4870) ∨ (¬ p5020))
    : (¬ p3654) ∨ (¬ p3954) ∨ (¬ p4026) ∨ (¬ p4870) ∨ (¬ p5020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4026 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5020 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20144 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48101 (p2027 p2982 p3680 p4282 p4321 p4702 p4938 : Prop)
    (h40810 : (¬ p2027))
    (h20164 : p2027 ∨ (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4282) ∨ (¬ p4321) ∨ (¬ p4702) ∨ (¬ p4938))
    : (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4282) ∨ (¬ p4321) ∨ (¬ p4702) ∨ (¬ p4938) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20164 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48105 (p2027 p2136 p2619 p2737 p3366 p4120 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h20184 : p2027 ∨ (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4120) ∨ (¬ p5049))
    : (¬ p2136) ∨ (¬ p2619) ∨ (¬ p2737) ∨ (¬ p3366) ∨ (¬ p4120) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4120 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20184 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48106 (p2027 p3343 p4256 p4348 p4438 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h20191 : p2027 ∨ (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695))
    : (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20191 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48108 (p2027 p2528 p3266 p4322 p4335 p4383 p4902 : Prop)
    (h40810 : (¬ p2027))
    (h20195 : p2027 ∨ (¬ p2528) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4383) ∨ (¬ p4902))
    : (¬ p2528) ∨ (¬ p3266) ∨ (¬ p4322) ∨ (¬ p4335) ∨ (¬ p4383) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20195 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48109 (p2027 p2138 p2470 p3362 p3364 p3874 p5049 : Prop)
    (h40810 : (¬ p2027))
    (h20197 : p2027 ∨ (¬ p2138) ∨ (¬ p2470) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p5049))
    : (¬ p2138) ∨ (¬ p2470) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p3874) ∨ (¬ p5049) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20197 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48110 (p2027 p2138 p3355 p3362 p3364 p5049 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h20198 : p2027 ∨ (¬ p2138) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p5049) ∨ (¬ p5160))
    : (¬ p2138) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3364) ∨ (¬ p5049) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3364 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5049 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20198 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48112 (p2027 p2144 p2657 p3212 p3680 p3742 p4444 p4669 p4789 p4829 p5503 : Prop)
    (h40810 : (¬ p2027))
    (h20202 : p2027 ∨ (¬ p2144) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4789) ∨ (¬ p4829) ∨ (¬ p5503))
    : (¬ p2144) ∨ (¬ p2657) ∨ (¬ p3212) ∨ (¬ p3680) ∨ (¬ p3742) ∨ (¬ p4444) ∨ (¬ p4669) ∨ (¬ p4789) ∨ (¬ p4829) ∨ (¬ p5503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20202 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48114 (p2027 p2542 p2659 p3222 p3238 p3346 : Prop)
    (h40810 : (¬ p2027))
    (h20207 : p2027 ∨ (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346))
    : (¬ p2542) ∨ (¬ p2659) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20207 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48116 (p2003 p2780 p2787 p3586 : Prop)
    (h2163 : p2003)
    (h40901 : (¬ p3586))
    (h20216 : (¬ p2003) ∨ (¬ p2780) ∨ p2787 ∨ p3586)
    : (¬ p2780) ∨ p2787 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2780 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2787) := (fun h => hn (Or.inr h));
    let u2 : p2003 := h2163;
    let u3 : (¬ p3586) := h40901;
    (Or.elim h20216 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u1 q2))) (fun r2 => (False.elim (u3 r2)))))))))

theorem step48117 (p2027 p2608 p3527 p3551 p3820 p3873 p4793 : Prop)
    (h40810 : (¬ p2027))
    (h20217 : p2027 ∨ (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4793))
    : (¬ p2608) ∨ (¬ p3527) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3873) ∨ (¬ p4793) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20217 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48118 (p2027 p2190 p3097 p3969 p4405 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h20219 : p2027 ∨ (¬ p2190) ∨ (¬ p3097) ∨ (¬ p3969) ∨ (¬ p4405) ∨ (¬ p5580))
    : (¬ p2190) ∨ (¬ p3097) ∨ (¬ p3969) ∨ (¬ p4405) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20219 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48124 (p2006 p2027 p2132 p2274 p2765 p2780 p3822 : Prop)
    (h2166 : p2006)
    (h40810 : (¬ p2027))
    (h40883 : (¬ p2765))
    (h20236 : (¬ p2006) ∨ p2027 ∨ (¬ p2132) ∨ (¬ p2274) ∨ p2765 ∨ (¬ p2780) ∨ (¬ p3822))
    : (¬ p2132) ∨ (¬ p2274) ∨ (¬ p2780) ∨ (¬ p3822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2780 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2006 := h2166;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2765) := h40883;
    (Or.elim h20236 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step48125 (p2027 p2138 p2946 p4111 p4117 p4243 p4365 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h20239 : p2027 ∨ (¬ p2138) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p4117) ∨ (¬ p4243) ∨ (¬ p4365) ∨ (¬ p4704))
    : (¬ p2138) ∨ (¬ p2946) ∨ (¬ p4111) ∨ (¬ p4117) ∨ (¬ p4243) ∨ (¬ p4365) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4243 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h20239 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step48126 (p2027 p3097 p3644 p3952 p4237 p4276 p4378 : Prop)
    (h40810 : (¬ p2027))
    (h20240 : p2027 ∨ (¬ p3097) ∨ (¬ p3644) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4276) ∨ (¬ p4378))
    : (¬ p3097) ∨ (¬ p3644) ∨ (¬ p3952) ∨ (¬ p4237) ∨ (¬ p4276) ∨ (¬ p4378) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3097 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20240 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48127 (p1979 p2027 p2657 p2727 p2749 p2946 p3586 p3688 : Prop)
    (h2139 : p1979)
    (h40810 : (¬ p2027))
    (h40901 : (¬ p3586))
    (h20243 : (¬ p1979) ∨ p2027 ∨ (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2946) ∨ p3586 ∨ (¬ p3688))
    : (¬ p2657) ∨ (¬ p2727) ∨ (¬ p2749) ∨ (¬ p2946) ∨ (¬ p3688) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2657 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1979 := h2139;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p3586) := h40901;
    (Or.elim h20243 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (u7 q6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48129 (p2027 p2946 p3027 p3414 p4111 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h20249 : p2027 ∨ (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4704))
    : (¬ p2946) ∨ (¬ p3027) ∨ (¬ p3414) ∨ (¬ p4111) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3414 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20249 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48130 (p2027 p2542 p2727 p4360 p4437 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h20261 : p2027 ∨ (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4608))
    : (¬ p2542) ∨ (¬ p2727) ∨ (¬ p4360) ∨ (¬ p4437) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20261 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48131 (p2027 p2341 p2396 p3644 p3821 p4276 : Prop)
    (h40810 : (¬ p2027))
    (h20263 : p2027 ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3644) ∨ (¬ p3821) ∨ (¬ p4276))
    : (¬ p2341) ∨ (¬ p2396) ∨ (¬ p3644) ∨ (¬ p3821) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3821 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20263 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48132 (p2027 p3325 p3644 p3979 p4276 p5558 : Prop)
    (h40810 : (¬ p2027))
    (h20264 : p2027 ∨ (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3979) ∨ (¬ p4276) ∨ (¬ p5558))
    : (¬ p3325) ∨ (¬ p3644) ∨ (¬ p3979) ∨ (¬ p4276) ∨ (¬ p5558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3325 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20264 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48135 (p2027 p2588 p2668 p3564 p4037 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h20294 : p2027 ∨ (¬ p2588) ∨ (¬ p2668) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4405))
    : (¬ p2588) ∨ (¬ p2668) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20294 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48136 (p2001 p2027 p2202 p2470 p2589 p3073 p3692 p4370 : Prop)
    (h2161 : p2001)
    (h40810 : (¬ p2027))
    (h40867 : (¬ p2202))
    (h20300 : (¬ p2001) ∨ p2027 ∨ p2202 ∨ (¬ p2470) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4370))
    : (¬ p2470) ∨ (¬ p2589) ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4370) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2001 := h2161;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2202) := h40867;
    (Or.elim h20300 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48137 (p2027 p2470 p2531 p2589 p4235 p4904 : Prop)
    (h40810 : (¬ p2027))
    (h20310 : p2027 ∨ (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p4904))
    : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2589) ∨ (¬ p4235) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20310 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48138 (p2027 p2230 p2440 p2579 p3422 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h20324 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4753))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3422) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20324 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48139 (p2027 p2850 p3367 p3583 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h20326 : p2027 ∨ (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4885))
    : (¬ p2850) ∨ (¬ p3367) ∨ (¬ p3583) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : (¬ p2027) := h40810;
    (Or.elim h20326 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step48140 (p1994 p2027 p2651 p2764 p3172 p4118 p4444 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40882 : (¬ p2764))
    (h20330 : (¬ p1994) ∨ p2027 ∨ (¬ p2651) ∨ p2764 ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4444))
    : (¬ p2651) ∨ (¬ p3172) ∨ (¬ p4118) ∨ (¬ p4444) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4444 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1994 := h2154;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2764) := h40882;
    (Or.elim h20330 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step48141 (p2027 p2210 p2284 p3591 p3957 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h20338 : p2027 ∨ (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4957))
    : (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3591) ∨ (¬ p3957) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20338 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48143 (p2027 p2132 p2737 p3425 p3583 p4778 : Prop)
    (h40810 : (¬ p2027))
    (h20345 : p2027 ∨ (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3425) ∨ (¬ p3583) ∨ (¬ p4778))
    : (¬ p2132) ∨ (¬ p2737) ∨ (¬ p3425) ∨ (¬ p3583) ∨ (¬ p4778) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3583 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4778 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20345 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48145 (p2027 p2156 p2177 p2247 p2274 p4111 p4256 p4438 p4521 : Prop)
    (h40810 : (¬ p2027))
    (h20377 : p2027 ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4521))
    : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2274) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4438) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20377 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48146 (p2027 p2406 p2476 p3193 p3355 p4608 : Prop)
    (h40810 : (¬ p2027))
    (h20381 : p2027 ∨ (¬ p2406) ∨ (¬ p2476) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p4608))
    : (¬ p2406) ∨ (¬ p2476) ∨ (¬ p3193) ∨ (¬ p3355) ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20381 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48147 (p2027 p2651 p2745 p2952 p3136 p4111 : Prop)
    (h40810 : (¬ p2027))
    (h20385 : p2027 ∨ (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4111))
    : (¬ p2651) ∨ (¬ p2745) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p4111) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20385 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48150 (p2027 p2807 p2963 p3097 p3552 p4560 : Prop)
    (h40810 : (¬ p2027))
    (h20403 : p2027 ∨ (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560))
    : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p3097) ∨ (¬ p3552) ∨ (¬ p4560) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3552 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4560 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20403 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48152 (p2027 p2387 p2668 p2946 p3019 p3983 p4704 : Prop)
    (h40810 : (¬ p2027))
    (h20411 : p2027 ∨ (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2946) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4704))
    : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2946) ∨ (¬ p3019) ∨ (¬ p3983) ∨ (¬ p4704) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4704 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20411 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48158 (p2027 p2717 p3027 p4360 p4548 p4783 : Prop)
    (h40810 : (¬ p2027))
    (h20429 : p2027 ∨ (¬ p2717) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4783))
    : (¬ p2717) ∨ (¬ p3027) ∨ (¬ p4360) ∨ (¬ p4548) ∨ (¬ p4783) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4783 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20429 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48159 (p2027 p2187 p2230 p2563 p3688 p3822 p3954 p4405 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h20431 : p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) ∨ (¬ p5190))
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2563) ∨ (¬ p3688) ∨ (¬ p3822) ∨ (¬ p3954) ∨ (¬ p4405) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3688 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20431 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48161 (p2027 p2156 p2247 p3125 p3461 p3892 p4111 p4521 p5133 : Prop)
    (h40810 : (¬ p2027))
    (h20439 : p2027 ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5133))
    : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5133) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3892 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20439 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48162 (p2027 p2156 p2247 p3125 p3461 p3892 p4111 p4521 p5127 : Prop)
    (h40810 : (¬ p2027))
    (h20440 : p2027 ∨ (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5127))
    : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5127) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3892 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20440 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48163 (p2027 p2177 p2507 p3309 p3581 p3644 : Prop)
    (h40810 : (¬ p2027))
    (h20446 : p2027 ∨ (¬ p2177) ∨ (¬ p2507) ∨ (¬ p3309) ∨ (¬ p3581) ∨ (¬ p3644))
    : (¬ p2177) ∨ (¬ p2507) ∨ (¬ p3309) ∨ (¬ p3581) ∨ (¬ p3644) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20446 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48164 (p2027 p3051 p3549 p3591 p4140 p4399 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h20447 : p2027 ∨ (¬ p3051) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4140) ∨ (¬ p4399) ∨ (¬ p5190))
    : (¬ p3051) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4140) ∨ (¬ p4399) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20447 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48165 (p2027 p2145 p2299 p2630 p2696 p3083 p3097 p3646 p4420 : Prop)
    (h40810 : (¬ p2027))
    (h20458 : p2027 ∨ (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420))
    : (¬ p2145) ∨ (¬ p2299) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p3083) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2299 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20458 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48166 (p2027 p2284 p2954 p3125 p3946 p4198 : Prop)
    (h40810 : (¬ p2027))
    (h20461 : p2027 ∨ (¬ p2284) ∨ (¬ p2954) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198))
    : (¬ p2284) ∨ (¬ p2954) ∨ (¬ p3125) ∨ (¬ p3946) ∨ (¬ p4198) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20461 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48168 (p2027 p2373 p2850 p3876 p4001 p4904 : Prop)
    (h40810 : (¬ p2027))
    (h20465 : p2027 ∨ (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p4904))
    : (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3876) ∨ (¬ p4001) ∨ (¬ p4904) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3876 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20465 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48169 (p2027 p2901 p3549 p3952 p4140 p4514 : Prop)
    (h40810 : (¬ p2027))
    (h20466 : p2027 ∨ (¬ p2901) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4514))
    : (¬ p2901) ∨ (¬ p3549) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4514) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4514 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20466 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48170 (p2027 p2934 p3238 p3527 p3644 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h20470 : p2027 ∨ (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4646))
    : (¬ p2934) ∨ (¬ p3238) ∨ (¬ p3527) ∨ (¬ p3644) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2934 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20470 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48171 (p2027 p2662 p2685 p2810 p3238 p3519 p3579 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h20472 : p2027 ∨ (¬ p2662) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3519) ∨ (¬ p3579) ∨ (¬ p4646))
    : (¬ p2662) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p3238) ∨ (¬ p3519) ∨ (¬ p3579) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3238 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3579 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h20472 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step48172 (p2027 p3609 p3857 p3988 p4110 p4115 p4744 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h20475 : p2027 ∨ (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4115) ∨ (¬ p4744) ∨ (¬ p4885))
    : (¬ p3609) ∨ (¬ p3857) ∨ (¬ p3988) ∨ (¬ p4110) ∨ (¬ p4115) ∨ (¬ p4744) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3857 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : (¬ p2027) := h40810;
    (Or.elim h20475 (fun q0 => (False.elim (u7 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step48174 (p2027 p2427 p2850 p2957 p3556 p4700 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h20482 : p2027 ∨ (¬ p2427) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4700) ∨ (¬ p4753))
    : (¬ p2427) ∨ (¬ p2850) ∨ (¬ p2957) ∨ (¬ p3556) ∨ (¬ p4700) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20482 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48175 (p2027 p2373 p2992 p4312 p4360 p4702 : Prop)
    (h40810 : (¬ p2027))
    (h20485 : p2027 ∨ (¬ p2373) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4702))
    : (¬ p2373) ∨ (¬ p2992) ∨ (¬ p4312) ∨ (¬ p4360) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4360 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20485 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48176 (p2027 p2860 p3212 p3646 p4244 p5104 : Prop)
    (h40810 : (¬ p2027))
    (h20486 : p2027 ∨ (¬ p2860) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p5104))
    : (¬ p2860) ∨ (¬ p3212) ∨ (¬ p3646) ∨ (¬ p4244) ∨ (¬ p5104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3212 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4244 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20486 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48177 (p2027 p2295 p3097 p4110 p4336 p4705 : Prop)
    (h40810 : (¬ p2027))
    (h20489 : p2027 ∨ (¬ p2295) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4705))
    : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4705) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20489 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48182 (p2027 p2417 p2598 p2668 p2753 p3201 p3923 p4037 p4625 p4870 : Prop)
    (h40810 : (¬ p2027))
    (h20510 : p2027 ∨ (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2668) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3923) ∨ (¬ p4037) ∨ (¬ p4625) ∨ (¬ p4870))
    : (¬ p2417) ∨ (¬ p2598) ∨ (¬ p2668) ∨ (¬ p2753) ∨ (¬ p3201) ∨ (¬ p3923) ∨ (¬ p4037) ∨ (¬ p4625) ∨ (¬ p4870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20510 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48184 (p2027 p2341 p3370 p3570 p4235 p4632 p4988 : Prop)
    (h40810 : (¬ p2027))
    (h20513 : p2027 ∨ (¬ p2341) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4632) ∨ (¬ p4988))
    : (¬ p2341) ∨ (¬ p3370) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4632) ∨ (¬ p4988) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20513 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48185 (p2027 p3399 p3555 p3571 p4235 p4632 : Prop)
    (h40810 : (¬ p2027))
    (h20517 : p2027 ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4235) ∨ (¬ p4632))
    : (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4235) ∨ (¬ p4632) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20517 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48186 (p2027 p2656 p3355 p4256 p4347 p4384 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h20526 : p2027 ∨ (¬ p2656) ∨ (¬ p3355) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695))
    : (¬ p2656) ∨ (¬ p3355) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2656 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20526 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48187 (p2027 p2144 p2156 p2190 p2657 p3146 p3644 p3742 p4133 p4347 p4789 : Prop)
    (h40810 : (¬ p2027))
    (h20527 : p2027 ∨ (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4789))
    : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2144 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20527 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48188 (p2027 p3343 p4133 p4256 p4347 p4383 p4695 : Prop)
    (h40810 : (¬ p2027))
    (h20529 : p2027 ∨ (¬ p3343) ∨ (¬ p4133) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4383) ∨ (¬ p4695))
    : (¬ p3343) ∨ (¬ p4133) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4383) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20529 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48189 (p2027 p3246 p3570 p4133 p4347 p4443 : Prop)
    (h40810 : (¬ p2027))
    (h20532 : p2027 ∨ (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443))
    : (¬ p3246) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4443) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4443 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20532 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48191 (p2027 p2928 p3389 p3402 p3591 p4079 p4756 : Prop)
    (h40810 : (¬ p2027))
    (h20534 : p2027 ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756))
    : (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3402) ∨ (¬ p3591) ∨ (¬ p4079) ∨ (¬ p4756) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2928 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3591 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4079 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20534 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48194 (p2027 p2307 p2352 p2387 p3822 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h20541 : p2027 ∨ (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3822) ∨ (¬ p5222))
    : (¬ p2307) ∨ (¬ p2352) ∨ (¬ p2387) ∨ (¬ p3822) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3822 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20541 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48195 (p2027 p2352 p2363 p2493 p2608 p3555 p4363 p4376 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h20553 : p2027 ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2493) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4376) ∨ (¬ p5059))
    : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2493) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p4363) ∨ (¬ p4376) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20553 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48196 (p2027 p2952 p3204 p3309 p3568 p3987 p4566 : Prop)
    (h40810 : (¬ p2027))
    (h20554 : p2027 ∨ (¬ p2952) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566))
    : (¬ p2952) ∨ (¬ p3204) ∨ (¬ p3309) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4566) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2952 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4566 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20554 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48199 (p2027 p2138 p2598 p3641 p3698 p4610 : Prop)
    (h40810 : (¬ p2027))
    (h20561 : p2027 ∨ (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3698) ∨ (¬ p4610))
    : (¬ p2138) ∨ (¬ p2598) ∨ (¬ p3641) ∨ (¬ p3698) ∨ (¬ p4610) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4610 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20561 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48200 (p2027 p2331 p2668 p3055 p3979 p4425 p4786 p5119 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h20566 : p2027 ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160))
    : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3979) ∨ (¬ p4425) ∨ (¬ p4786) ∨ (¬ p5119) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3055 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20566 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48202 (p2027 p2307 p2387 p2588 p2819 p5225 : Prop)
    (h40810 : (¬ p2027))
    (h20572 : p2027 ∨ (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2819) ∨ (¬ p5225))
    : (¬ p2307) ∨ (¬ p2387) ∨ (¬ p2588) ∨ (¬ p2819) ∨ (¬ p5225) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5225 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20572 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48204 (p2027 p2230 p2440 p3083 p3588 p3659 p3954 p4420 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h20580 : p2027 ∨ (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4420) ∨ (¬ p5190))
    : (¬ p2230) ∨ (¬ p2440) ∨ (¬ p3083) ∨ (¬ p3588) ∨ (¬ p3659) ∨ (¬ p3954) ∨ (¬ p4420) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20580 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48205 (p2027 p2156 p2901 p3952 p4032 p5102 : Prop)
    (h40810 : (¬ p2027))
    (h20586 : p2027 ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4032) ∨ (¬ p5102))
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4032) ∨ (¬ p5102) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5102 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20586 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48206 (p2027 p2156 p2901 p3370 p3952 p4363 p5102 : Prop)
    (h40810 : (¬ p2027))
    (h20587 : p2027 ∨ (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3370) ∨ (¬ p3952) ∨ (¬ p4363) ∨ (¬ p5102))
    : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3370) ∨ (¬ p3952) ∨ (¬ p4363) ∨ (¬ p5102) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5102 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20587 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48209 (p2027 p3692 p3830 p3860 p4352 p4498 : Prop)
    (h40810 : (¬ p2027))
    (h20591 : p2027 ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4498))
    : (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3860) ∨ (¬ p4352) ∨ (¬ p4498) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3692 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4498 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20591 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48211 (p2027 p3063 p3093 p3834 p3945 p4133 p5358 : Prop)
    (h40810 : (¬ p2027))
    (h20593 : p2027 ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p5358))
    : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3834) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p5358) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3834 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20593 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48215 (p2027 p2542 p3051 p3486 p4109 p4202 p4811 : Prop)
    (h40810 : (¬ p2027))
    (h20607 : p2027 ∨ (¬ p2542) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811))
    : (¬ p2542) ∨ (¬ p3051) ∨ (¬ p3486) ∨ (¬ p4109) ∨ (¬ p4202) ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4202 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20607 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48216 (p2027 p2589 p2850 p3471 p3905 p5086 : Prop)
    (h40810 : (¬ p2027))
    (h20616 : p2027 ∨ (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3471) ∨ (¬ p3905) ∨ (¬ p5086))
    : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p3471) ∨ (¬ p3905) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20616 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48217 (p2027 p2187 p2230 p2247 p2563 p2996 p3553 p4133 p5190 : Prop)
    (h40810 : (¬ p2027))
    (h20624 : p2027 ∨ (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p5190))
    : (¬ p2187) ∨ (¬ p2230) ∨ (¬ p2247) ∨ (¬ p2563) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4133) ∨ (¬ p5190) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20624 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48218 (p2027 p2383 p2781 p3292 p3564 p3680 p3956 p4236 p4368 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h20630 : p2027 ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3292) ∨ (¬ p3564) ∨ (¬ p3680) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4368) ∨ (¬ p5284))
    : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3292) ∨ (¬ p3564) ∨ (¬ p3680) ∨ (¬ p3956) ∨ (¬ p4236) ∨ (¬ p4368) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20630 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48220 (p2027 p2138 p2331 p3506 p3694 p4191 p4200 p4330 p4421 p4786 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h20640 : p2027 ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4191) ∨ (¬ p4200) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5568))
    : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4191) ∨ (¬ p4200) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4200 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20640 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48221 (p2027 p2138 p2331 p3506 p3694 p4421 p4786 p5117 p5568 : Prop)
    (h40810 : (¬ p2027))
    (h20641 : p2027 ∨ (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5117) ∨ (¬ p5568))
    : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p3506) ∨ (¬ p3694) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5117) ∨ (¬ p5568) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20641 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48222 (p2027 p2363 p2383 p3266 p3365 p3366 p4315 p4866 p5016 p5405 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h20649 : p2027 ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20649 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48224 (p2027 p2363 p3692 p4119 p4129 p4138 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h20657 : p2027 ∨ (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4129) ∨ (¬ p4138) ∨ (¬ p5564))
    : (¬ p2363) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4129) ∨ (¬ p4138) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4129 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20657 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48225 (p2027 p2459 p2881 p3919 p4118 p4280 : Prop)
    (h40810 : (¬ p2027))
    (h20658 : p2027 ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4280))
    : (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3919) ∨ (¬ p4118) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3919 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20658 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48226 (p2027 p2696 p2753 p3136 p3549 p4107 p4272 p4381 p4870 p5400 : Prop)
    (h40810 : (¬ p2027))
    (h20661 : p2027 ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4272) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400))
    : (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4272) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4272 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20661 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48227 (p2027 p2284 p2696 p2753 p3136 p3549 p4107 p4381 p4870 p5400 p5448 : Prop)
    (h40810 : (¬ p2027))
    (h20662 : p2027 ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) ∨ (¬ p5448))
    : (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3549) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400) ∨ (¬ p5448) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4107 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4381 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5448 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20662 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48228 (p2027 p2122 p3097 p3985 p4110 p4885 : Prop)
    (h40810 : (¬ p2027))
    (h20665 : p2027 ∨ (¬ p2122) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4110) ∨ (¬ p4885))
    : (¬ p2122) ∨ (¬ p3097) ∨ (¬ p3985) ∨ (¬ p4110) ∨ (¬ p4885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3985 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20665 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48229 (p2027 p2751 p3038 p3527 p3553 p3572 : Prop)
    (h40810 : (¬ p2027))
    (h20673 : p2027 ∨ (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p3572))
    : (¬ p2751) ∨ (¬ p3038) ∨ (¬ p3527) ∨ (¬ p3553) ∨ (¬ p3572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2751 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20673 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48230 (p2027 p3063 p3093 p4366 p4405 p4427 : Prop)
    (h40810 : (¬ p2027))
    (h20674 : p2027 ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4427))
    : (¬ p3063) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4405) ∨ (¬ p4427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20674 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48231 (p2027 p2145 p2563 p2717 p3471 p3553 p3646 p4235 p4280 : Prop)
    (h40810 : (¬ p2027))
    (h20677 : p2027 ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4280))
    : (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2717) ∨ (¬ p3471) ∨ (¬ p3553) ∨ (¬ p3646) ∨ (¬ p4235) ∨ (¬ p4280) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2145 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4235 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4280 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20677 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48233 (p2027 p2651 p2743 p2810 p4117 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h20680 : p2027 ∨ (¬ p2651) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4737))
    : (¬ p2651) ∨ (¬ p2743) ∨ (¬ p2810) ∨ (¬ p4117) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2810 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20680 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48235 (p2027 p2387 p2406 p2982 p3266 p3322 p3379 p4191 p4450 p5021 : Prop)
    (h40810 : (¬ p2027))
    (h20682 : p2027 ∨ (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3379) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021))
    : (¬ p2387) ∨ (¬ p2406) ∨ (¬ p2982) ∨ (¬ p3266) ∨ (¬ p3322) ∨ (¬ p3379) ∨ (¬ p4191) ∨ (¬ p4450) ∨ (¬ p5021) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5021 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20682 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48236 (p2027 p2363 p3266 p4321 p4335 p4387 p4433 : Prop)
    (h40810 : (¬ p2027))
    (h20691 : p2027 ∨ (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4321) ∨ (¬ p4335) ∨ (¬ p4387) ∨ (¬ p4433))
    : (¬ p2363) ∨ (¬ p3266) ∨ (¬ p4321) ∨ (¬ p4335) ∨ (¬ p4387) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20691 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48237 (p2027 p2363 p3685 p4138 p4253 p4340 p5564 : Prop)
    (h40810 : (¬ p2027))
    (h20698 : p2027 ∨ (¬ p2363) ∨ (¬ p3685) ∨ (¬ p4138) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p5564))
    : (¬ p2363) ∨ (¬ p3685) ∨ (¬ p4138) ∨ (¬ p4253) ∨ (¬ p4340) ∨ (¬ p5564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4340 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20698 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48243 (p1992 p2997 p3549 p4866 : Prop)
    (h2152 : p1992)
    (h40890 : (¬ p2997))
    (h20711 : (¬ p1992) ∨ p2997 ∨ (¬ p3549) ∨ p4866)
    : (¬ p3549) ∨ p4866 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3549 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4866) := (fun h => hn (Or.inr h));
    let u2 : p1992 := h2152;
    let u3 : (¬ p2997) := h40890;
    (Or.elim h20711 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48246 (p2027 p2139 p2156 p2274 p2396 p2476 p3641 p3905 p4641 p5160 : Prop)
    (h40810 : (¬ p2027))
    (h20732 : p2027 ∨ (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160))
    : (¬ p2139) ∨ (¬ p2156) ∨ (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2476) ∨ (¬ p3641) ∨ (¬ p3905) ∨ (¬ p4641) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2139 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2476 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : (¬ p2027) := h40810;
    (Or.elim h20732 (fun q0 => (False.elim (u9 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step48248 (p2027 p3073 p3692 p4119 p4320 p4496 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h20735 : p2027 ∨ (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4496) ∨ (¬ p4960))
    : (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4320) ∨ (¬ p4496) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4496 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20735 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48252 (p2027 p2138 p3471 p3694 p4344 p4901 : Prop)
    (h40810 : (¬ p2027))
    (h20745 : p2027 ∨ (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3694) ∨ (¬ p4344) ∨ (¬ p4901))
    : (¬ p2138) ∨ (¬ p3471) ∨ (¬ p3694) ∨ (¬ p4344) ∨ (¬ p4901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2138 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3694 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20745 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48254 (p2027 p2437 p2573 p2589 p3574 p4646 : Prop)
    (h40810 : (¬ p2027))
    (h20748 : p2027 ∨ (¬ p2437) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4646))
    : (¬ p2437) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3574) ∨ (¬ p4646) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20748 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48255 (p2027 p3692 p3969 p4191 p4330 p5121 : Prop)
    (h40810 : (¬ p2027))
    (h20751 : p2027 ∨ (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p5121))
    : (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p5121) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3692 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20751 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48257 (p2027 p2241 p2307 p2396 p2761 p3412 p3555 p4756 p5016 p5405 p5740 : Prop)
    (h40810 : (¬ p2027))
    (h20755 : p2027 ∨ (¬ p2241) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4756) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p2241) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4756) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20755 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48258 (p2027 p2470 p2509 p2630 p2656 p2745 p3402 : Prop)
    (h40810 : (¬ p2027))
    (h20761 : p2027 ∨ (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402))
    : (¬ p2470) ∨ (¬ p2509) ∨ (¬ p2630) ∨ (¬ p2656) ∨ (¬ p2745) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20761 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48260 (p2027 p2298 p2383 p2797 p3567 p3572 p4405 : Prop)
    (h40810 : (¬ p2027))
    (h20764 : p2027 ∨ (¬ p2298) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p4405))
    : (¬ p2298) ∨ (¬ p2383) ∨ (¬ p2797) ∨ (¬ p3567) ∨ (¬ p3572) ∨ (¬ p4405) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2298 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20764 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48261 (p2027 p2230 p2373 p3365 p3877 p3969 p4118 p4419 p5122 : Prop)
    (h40810 : (¬ p2027))
    (h20767 : p2027 ∨ (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3969) ∨ (¬ p4118) ∨ (¬ p4419) ∨ (¬ p5122))
    : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3969) ∨ (¬ p4118) ∨ (¬ p4419) ∨ (¬ p5122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3969 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20767 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48265 (p2027 p2132 p2860 p3125 p3266 p3292 p4330 p4789 p5284 : Prop)
    (h40810 : (¬ p2027))
    (h20772 : p2027 ∨ (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p5284))
    : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p5284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2132 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3292 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20772 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48266 (p2027 p2230 p2963 p3105 p3324 p3362 p3680 p3698 p4789 p5123 p5580 : Prop)
    (h40810 : (¬ p2027))
    (h20773 : p2027 ∨ (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5580))
    : (¬ p2230) ∨ (¬ p2963) ∨ (¬ p3105) ∨ (¬ p3324) ∨ (¬ p3362) ∨ (¬ p3680) ∨ (¬ p3698) ∨ (¬ p4789) ∨ (¬ p5123) ∨ (¬ p5580) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2963 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : (¬ p2027) := h40810;
    (Or.elim h20773 (fun q0 => (False.elim (u10 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u7))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u8))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step48268 (p2027 p2177 p2247 p2307 p2459 p3662 p4208 p5017 p5059 : Prop)
    (h40810 : (¬ p2027))
    (h20778 : p2027 ∨ (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5017) ∨ (¬ p5059))
    : (¬ p2177) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p3662) ∨ (¬ p4208) ∨ (¬ p5017) ∨ (¬ p5059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2247 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4208 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : (¬ p2027) := h40810;
    (Or.elim h20778 (fun q0 => (False.elim (u8 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step48270 (p2010 p2027 p2233 p2482 p3201 p3874 p3998 p4286 : Prop)
    (h2170 : p2010)
    (h40810 : (¬ p2027))
    (h40868 : (¬ p2233))
    (h20786 : (¬ p2010) ∨ p2027 ∨ p2233 ∨ (¬ p2482) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3998) ∨ (¬ p4286))
    : (¬ p2482) ∨ (¬ p3201) ∨ (¬ p3874) ∨ (¬ p3998) ∨ (¬ p4286) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2482 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3874 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3998 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2010 := h2170;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2233) := h40868;
    (Or.elim h20786 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48271 (p1998 p2169 p2177 p4501 : Prop)
    (h2158 : p1998)
    (h40866 : (¬ p2169))
    (h20788 : (¬ p1998) ∨ p2169 ∨ (¬ p2177) ∨ p4501)
    : (¬ p2177) ∨ p4501 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4501) := (fun h => hn (Or.inr h));
    let u2 : p1998 := h2158;
    let u3 : (¬ p2169) := h40866;
    (Or.elim h20788 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48272 (p2003 p2323 p2331 p4581 : Prop)
    (h2163 : p2003)
    (h40870 : (¬ p2323))
    (h20789 : (¬ p2003) ∨ p2323 ∨ (¬ p2331) ∨ p4581)
    : (¬ p2331) ∨ p4581 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4581) := (fun h => hn (Or.inr h));
    let u2 : p2003 := h2163;
    let u3 : (¬ p2323) := h40870;
    (Or.elim h20789 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48273 (p1978 p2344 p3646 p4489 : Prop)
    (h2138 : p1978)
    (h40871 : (¬ p2344))
    (h20790 : (¬ p1978) ∨ p2344 ∨ (¬ p3646) ∨ p4489)
    : (¬ p3646) ∨ p4489 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3646 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4489) := (fun h => hn (Or.inr h));
    let u2 : p1978 := h2138;
    let u3 : (¬ p2344) := h40871;
    (Or.elim h20790 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48274 (p1992 p2608 p2611 p4733 : Prop)
    (h2152 : p1992)
    (h40877 : (¬ p2611))
    (h20791 : (¬ p1992) ∨ (¬ p2608) ∨ p2611 ∨ p4733)
    : (¬ p2608) ∨ p4733 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4733) := (fun h => hn (Or.inr h));
    let u2 : p1992 := h2152;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h20791 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48275 (p1986 p2622 p2630 p4750 : Prop)
    (h2146 : p1986)
    (h40878 : (¬ p2622))
    (h20792 : (¬ p1986) ∨ p2622 ∨ (¬ p2630) ∨ p4750)
    : (¬ p2630) ∨ p4750 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4750) := (fun h => hn (Or.inr h));
    let u2 : p1986 := h2146;
    let u3 : (¬ p2622) := h40878;
    (Or.elim h20792 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48276 (p2027 p2743 p2807 p3572 p4117 p4737 : Prop)
    (h40810 : (¬ p2027))
    (h20793 : p2027 ∨ (¬ p2743) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4737))
    : (¬ p2743) ∨ (¬ p2807) ∨ (¬ p3572) ∨ (¬ p4117) ∨ (¬ p4737) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2743 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20793 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48277 (p1984 p2611 p3954 p4737 : Prop)
    (h2144 : p1984)
    (h40877 : (¬ p2611))
    (h20794 : (¬ p1984) ∨ p2611 ∨ (¬ p3954) ∨ p4737)
    : (¬ p3954) ∨ p4737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4737) := (fun h => hn (Or.inr h));
    let u2 : p1984 := h2144;
    let u3 : (¬ p2611) := h40877;
    (Or.elim h20794 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48278 (p2006 p2842 p2850 p4882 : Prop)
    (h2166 : p2006)
    (h40885 : (¬ p2842))
    (h20795 : (¬ p2006) ∨ p2842 ∨ (¬ p2850) ∨ p4882)
    : (¬ p2850) ∨ p4882 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4882) := (fun h => hn (Or.inr h));
    let u2 : p2006 := h2166;
    let u3 : (¬ p2842) := h40885;
    (Or.elim h20795 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48279 (p1998 p2027 p2608 p2699 p2707 p3609 p4348 p4805 : Prop)
    (h2158 : p1998)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h20796 : (¬ p1998) ∨ p2027 ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2707) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4805))
    : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3609) ∨ (¬ p4348) ∨ (¬ p4805) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4805 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1998 := h2158;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2699) := h40881;
    (Or.elim h20796 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48280 (p1992 p2873 p3583 p4878 : Prop)
    (h2152 : p1992)
    (h40886 : (¬ p2873))
    (h20797 : (¬ p1992) ∨ p2873 ∨ (¬ p3583) ∨ p4878)
    : (¬ p3583) ∨ p4878 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3583 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4878) := (fun h => hn (Or.inr h));
    let u2 : p1992 := h2152;
    let u3 : (¬ p2873) := h40886;
    (Or.elim h20797 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48281 (p2027 p2807 p2952 p3486 p4333 p4957 : Prop)
    (h40810 : (¬ p2027))
    (h20798 : p2027 ∨ (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3486) ∨ (¬ p4333) ∨ (¬ p4957))
    : (¬ p2807) ∨ (¬ p2952) ∨ (¬ p3486) ∨ (¬ p4333) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3486 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20798 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48282 (p1977 p2027 p2651 p2911 p2914 p3551 p4111 p4849 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40887 : (¬ p2914))
    (h20799 : (¬ p1977) ∨ p2027 ∨ (¬ p2651) ∨ (¬ p2911) ∨ p2914 ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4849))
    : (¬ p2651) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4111) ∨ (¬ p4849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4111 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4849 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2914) := h40887;
    (Or.elim h20799 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u7 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48283 (p2027 p2295 p2881 p3324 p4138 p4559 : Prop)
    (h40810 : (¬ p2027))
    (h20801 : p2027 ∨ (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4559))
    : (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3324 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20801 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48284 (p2027 p2255 p2958 p3051 p3662 p4320 : Prop)
    (h40810 : (¬ p2027))
    (h20802 : p2027 ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3662) ∨ (¬ p4320))
    : (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3662) ∨ (¬ p4320) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20802 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48285 (p1976 p2114 p3954 p4736 : Prop)
    (h2136 : p1976)
    (h40864 : (¬ p2114))
    (h20803 : (¬ p1976) ∨ p2114 ∨ (¬ p3954) ∨ p4736)
    : (¬ p3954) ∨ p4736 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4736) := (fun h => hn (Or.inr h));
    let u2 : p1976 := h2136;
    let u3 : (¬ p2114) := h40864;
    (Or.elim h20803 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48286 (p2007 p3042 p3083 p5008 : Prop)
    (h2167 : p2007)
    (h40892 : (¬ p3042))
    (h20804 : (¬ p2007) ∨ p3042 ∨ (¬ p3083) ∨ p5008)
    : (¬ p3083) ∨ p5008 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5008) := (fun h => hn (Or.inr h));
    let u2 : p2007 := h2167;
    let u3 : (¬ p3042) := h40892;
    (Or.elim h20804 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48287 (p2011 p3128 p3744 p5046 : Prop)
    (h2171 : p2011)
    (h40894 : (¬ p3128))
    (h20805 : (¬ p2011) ∨ p3128 ∨ (¬ p3744) ∨ p5046)
    : (¬ p3744) ∨ p5046 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3744 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5046) := (fun h => hn (Or.inr h));
    let u2 : p2011 := h2171;
    let u3 : (¬ p3128) := h40894;
    (Or.elim h20805 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48288 (p1977 p2027 p2766 p2946 p3172 p3662 p3692 p4312 : Prop)
    (h2137 : p1977)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h20806 : (¬ p1977) ∨ p2027 ∨ p2766 ∨ (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4312))
    : (¬ p2946) ∨ (¬ p3172) ∨ (¬ p3662) ∨ (¬ p3692) ∨ (¬ p4312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3692 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1977 := h2137;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h20806 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u7 q2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48289 (p2005 p2588 p2914 p4712 : Prop)
    (h2165 : p2005)
    (h40887 : (¬ p2914))
    (h20807 : (¬ p2005) ∨ (¬ p2588) ∨ p2914 ∨ p4712)
    : (¬ p2588) ∨ p4712 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4712) := (fun h => hn (Or.inr h));
    let u2 : p2005 := h2165;
    let u3 : (¬ p2914) := h40887;
    (Or.elim h20807 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48290 (p2027 p2383 p2584 p2665 p3574 p3956 : Prop)
    (h40810 : (¬ p2027))
    (h20808 : p2027 ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3574) ∨ (¬ p3956))
    : (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2665) ∨ (¬ p3574) ∨ (¬ p3956) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3574 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3956 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20808 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48291 (p2027 p2528 p2881 p3690 p4438 p4445 : Prop)
    (h40810 : (¬ p2027))
    (h20809 : p2027 ∨ (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p4438) ∨ (¬ p4445))
    : (¬ p2528) ∨ (¬ p2881) ∨ (¬ p3690) ∨ (¬ p4438) ∨ (¬ p4445) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3690 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20809 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48292 (p2027 p2255 p2651 p3193 p3343 p3402 : Prop)
    (h40810 : (¬ p2027))
    (h20810 : p2027 ∨ (¬ p2255) ∨ (¬ p2651) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402))
    : (¬ p2255) ∨ (¬ p2651) ∨ (¬ p3193) ∨ (¬ p3343) ∨ (¬ p3402) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20810 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48293 (p2027 p2321 p2341 p2459 p3955 p4347 : Prop)
    (h40810 : (¬ p2027))
    (h20811 : p2027 ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3955) ∨ (¬ p4347))
    : (¬ p2321) ∨ (¬ p2341) ∨ (¬ p2459) ∨ (¬ p3955) ∨ (¬ p4347) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2321 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20811 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48294 (p2000 p2842 p3055 p4729 : Prop)
    (h2160 : p2000)
    (h40885 : (¬ p2842))
    (h20812 : (¬ p2000) ∨ p2842 ∨ (¬ p3055) ∨ p4729)
    : (¬ p3055) ∨ p4729 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3055 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4729) := (fun h => hn (Or.inr h));
    let u2 : p2000 := h2160;
    let u3 : (¬ p2842) := h40885;
    (Or.elim h20812 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48295 (p1997 p2388 p2542 p4701 : Prop)
    (h2157 : p1997)
    (h40873 : (¬ p2388))
    (h20813 : (¬ p1997) ∨ p2388 ∨ (¬ p2542) ∨ p4701)
    : (¬ p2542) ∨ p4701 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2542 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4701) := (fun h => hn (Or.inr h));
    let u2 : p1997 := h2157;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h20813 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48296 (p2027 p2553 p2829 p3588 p4471 p5222 : Prop)
    (h40810 : (¬ p2027))
    (h20814 : p2027 ∨ (¬ p2553) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4471) ∨ (¬ p5222))
    : (¬ p2553) ∨ (¬ p2829) ∨ (¬ p3588) ∨ (¬ p4471) ∨ (¬ p5222) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4471 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5222 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20814 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48297 (p2027 p2274 p2321 p2341 p3989 p4138 : Prop)
    (h40810 : (¬ p2027))
    (h20815 : p2027 ∨ (¬ p2274) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3989) ∨ (¬ p4138))
    : (¬ p2274) ∨ (¬ p2321) ∨ (¬ p2341) ∨ (¬ p3989) ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3989 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20815 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48298 (p1984 p2233 p3452 p5194 : Prop)
    (h2144 : p1984)
    (h40868 : (¬ p2233))
    (h20817 : (¬ p1984) ∨ p2233 ∨ (¬ p3452) ∨ p5194)
    : (¬ p3452) ∨ p5194 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5194) := (fun h => hn (Or.inr h));
    let u2 : p1984 := h2144;
    let u3 : (¬ p2233) := h40868;
    (Or.elim h20817 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48299 (p1977 p2409 p4111 p4814 : Prop)
    (h2137 : p1977)
    (h40874 : (¬ p2409))
    (h20818 : (¬ p1977) ∨ p2409 ∨ (¬ p4111) ∨ p4814)
    : (¬ p4111) ∨ p4814 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4111 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4814) := (fun h => hn (Or.inr h));
    let u2 : p1977 := h2137;
    let u3 : (¬ p2409) := h40874;
    (Or.elim h20818 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48300 (p1991 p2344 p2963 p4584 : Prop)
    (h2151 : p1991)
    (h40871 : (¬ p2344))
    (h20819 : (¬ p1991) ∨ p2344 ∨ (¬ p2963) ∨ p4584)
    : (¬ p2963) ∨ p4584 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2963 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4584) := (fun h => hn (Or.inr h));
    let u2 : p1991 := h2151;
    let u3 : (¬ p2344) := h40871;
    (Or.elim h20819 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48301 (p2027 p2299 p2319 p2341 p3567 p4037 p4620 : Prop)
    (h40810 : (¬ p2027))
    (h20820 : p2027 ∨ (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3567) ∨ (¬ p4037) ∨ (¬ p4620))
    : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p3567) ∨ (¬ p4037) ∨ (¬ p4620) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3567 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4037 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20820 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48302 (p1994 p2027 p2341 p2630 p2688 p3027 p3659 p4066 p4357 : Prop)
    (h2154 : p1994)
    (h40810 : (¬ p2027))
    (h40880 : (¬ p2688))
    (h20821 : (¬ p1994) ∨ p2027 ∨ (¬ p2341) ∨ (¬ p2630) ∨ p2688 ∨ (¬ p3027) ∨ (¬ p3659) ∨ (¬ p4066) ∨ (¬ p4357))
    : (¬ p2341) ∨ (¬ p2630) ∨ (¬ p3027) ∨ (¬ p3659) ∨ (¬ p4066) ∨ (¬ p4357) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3027 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p1994 := h2154;
    let u7 : (¬ p2027) := h40810;
    let u8 : (¬ p2688) := h40880;
    (Or.elim h20821 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u7 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u8 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step48303 (p1976 p2608 p2699 p4734 : Prop)
    (h2136 : p1976)
    (h40881 : (¬ p2699))
    (h20823 : (¬ p1976) ∨ (¬ p2608) ∨ p2699 ∨ p4734)
    : (¬ p2608) ∨ p4734 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4734) := (fun h => hn (Or.inr h));
    let u2 : p1976 := h2136;
    let u3 : (¬ p2699) := h40881;
    (Or.elim h20823 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u3 q2))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48304 (p2004 p3437 p3588 p4796 : Prop)
    (h2164 : p2004)
    (h40896 : (¬ p3437))
    (h20824 : (¬ p2004) ∨ p3437 ∨ (¬ p3588) ∨ p4796)
    : (¬ p3588) ∨ p4796 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3588 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4796) := (fun h => hn (Or.inr h));
    let u2 : p2004 := h2164;
    let u3 : (¬ p3437) := h40896;
    (Or.elim h20824 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48305 (p1984 p2344 p3591 p5022 : Prop)
    (h2144 : p1984)
    (h40871 : (¬ p2344))
    (h20825 : (¬ p1984) ∨ p2344 ∨ (¬ p3591) ∨ p5022)
    : (¬ p3591) ∨ p5022 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3591 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5022) := (fun h => hn (Or.inr h));
    let u2 : p1984 := h2144;
    let u3 : (¬ p2344) := h40871;
    (Or.elim h20825 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48306 (p1999 p2462 p4107 p4624 : Prop)
    (h2159 : p1999)
    (h40875 : (¬ p2462))
    (h20826 : (¬ p1999) ∨ p2462 ∨ (¬ p4107) ∨ p4624)
    : (¬ p4107) ∨ p4624 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4107 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4624) := (fun h => hn (Or.inr h));
    let u2 : p1999 := h2159;
    let u3 : (¬ p2462) := h40875;
    (Or.elim h20826 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48307 (p2027 p2177 p2274 p3744 p4396 p4666 : Prop)
    (h40810 : (¬ p2027))
    (h20827 : p2027 ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4666))
    : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p3744) ∨ (¬ p4396) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20827 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48308 (p1989 p2027 p2563 p2766 p3880 p4173 p4347 p4506 : Prop)
    (h2149 : p1989)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h20828 : (¬ p1989) ∨ p2027 ∨ (¬ p2563) ∨ p2766 ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506))
    : (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3880 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4173 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1989 := h2149;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h20828 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48309 (p2027 p2177 p2307 p3548 p4105 p5022 : Prop)
    (h40810 : (¬ p2027))
    (h20830 : p2027 ∨ (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p5022))
    : (¬ p2177) ∨ (¬ p2307) ∨ (¬ p3548) ∨ (¬ p4105) ∨ (¬ p5022) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20830 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48310 (p2027 p2982 p3097 p4110 p4624 p5045 : Prop)
    (h40810 : (¬ p2027))
    (h20831 : p2027 ∨ (¬ p2982) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4624) ∨ (¬ p5045))
    : (¬ p2982) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4624) ∨ (¬ p5045) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3097 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4110 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20831 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48312 (p2027 p3399 p3555 p3571 p4320 p4960 : Prop)
    (h40810 : (¬ p2027))
    (h20833 : p2027 ∨ (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p4960))
    : (¬ p3399) ∨ (¬ p3555) ∨ (¬ p3571) ∨ (¬ p4320) ∨ (¬ p4960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4320 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20833 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48313 (p2027 p2255 p2264 p2807 p3031 p3548 : Prop)
    (h40810 : (¬ p2027))
    (h20835 : p2027 ∨ (¬ p2255) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3031) ∨ (¬ p3548))
    : (¬ p2255) ∨ (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3031) ∨ (¬ p3548) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3548 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20835 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48314 (p2027 p2255 p2341 p2996 p3553 p4104 : Prop)
    (h40810 : (¬ p2027))
    (h20836 : p2027 ∨ (¬ p2255) ∨ (¬ p2341) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4104))
    : (¬ p2255) ∨ (¬ p2341) ∨ (¬ p2996) ∨ (¬ p3553) ∨ (¬ p4104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2996 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20836 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48316 (p2027 p2255 p2307 p3568 p3987 p4154 : Prop)
    (h40810 : (¬ p2027))
    (h20840 : p2027 ∨ (¬ p2255) ∨ (¬ p2307) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4154))
    : (¬ p2255) ∨ (¬ p2307) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4154) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3568 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3987 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4154 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20840 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48317 (p2027 p2255 p2295 p2331 p3549 p4245 : Prop)
    (h40810 : (¬ p2027))
    (h20841 : p2027 ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3549) ∨ (¬ p4245))
    : (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3549) ∨ (¬ p4245) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2255 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3549 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4245 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20841 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48318 (p2006 p2388 p4315 p5052 : Prop)
    (h2166 : p2006)
    (h40873 : (¬ p2388))
    (h20842 : (¬ p2006) ∨ p2388 ∨ (¬ p4315) ∨ p5052)
    : (¬ p4315) ∨ p5052 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4315 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5052) := (fun h => hn (Or.inr h));
    let u2 : p2006 := h2166;
    let u3 : (¬ p2388) := h40873;
    (Or.elim h20842 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48320 (p2027 p2589 p2829 p3363 p3585 p4390 p4717 : Prop)
    (h40810 : (¬ p2027))
    (h20844 : p2027 ∨ (¬ p2589) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4717))
    : (¬ p2589) ∨ (¬ p2829) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4390) ∨ (¬ p4717) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2589 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4390 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : (¬ p2027) := h40810;
    (Or.elim h20844 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step48323 (p2027 p2264 p2954 p2995 p3556 p3570 : Prop)
    (h40810 : (¬ p2027))
    (h20847 : p2027 ∨ (¬ p2264) ∨ (¬ p2954) ∨ (¬ p2995) ∨ (¬ p3556) ∨ (¬ p3570))
    : (¬ p2264) ∨ (¬ p2954) ∨ (¬ p2995) ∨ (¬ p3556) ∨ (¬ p3570) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2995 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3570 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20847 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48324 (p2002 p2622 p2797 p4843 : Prop)
    (h2162 : p2002)
    (h40878 : (¬ p2622))
    (h20849 : (¬ p2002) ∨ p2622 ∨ (¬ p2797) ∨ p4843)
    : (¬ p2797) ∨ p4843 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4843) := (fun h => hn (Or.inr h));
    let u2 : p2002 := h2162;
    let u3 : (¬ p2622) := h40878;
    (Or.elim h20849 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48326 (p1987 p2027 p2737 p2766 p3551 p3588 p3959 p4348 : Prop)
    (h2147 : p1987)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h20851 : (¬ p1987) ∨ p2027 ∨ (¬ p2737) ∨ p2766 ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p4348))
    : (¬ p2737) ∨ (¬ p3551) ∨ (¬ p3588) ∨ (¬ p3959) ∨ (¬ p4348) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3551 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3588 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3959 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4348 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p1987 := h2147;
    let u6 : (¬ p2027) := h40810;
    let u7 : (¬ p2766) := h40884;
    (Or.elim h20851 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u6 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u7 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step48327 (p1987 p2611 p2696 p3547 p5142 : Prop)
    (h2147 : p1987)
    (h40877 : (¬ p2611))
    (h20852 : (¬ p1987) ∨ p2611 ∨ (¬ p2696) ∨ (¬ p3547) ∨ p5142)
    : (¬ p2696) ∨ (¬ p3547) ∨ p5142 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3547 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p5142) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p1987 := h2147;
    let u4 : (¬ p2611) := h40877;
    (Or.elim h20852 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (u2 r3)))))))))))

theorem step48328 (p1985 p2027 p2427 p2608 p2699 p2850 p3367 : Prop)
    (h2145 : p1985)
    (h40810 : (¬ p2027))
    (h40881 : (¬ p2699))
    (h20853 : (¬ p1985) ∨ p2027 ∨ (¬ p2427) ∨ (¬ p2608) ∨ p2699 ∨ (¬ p2850) ∨ (¬ p3367))
    : (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2850) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1985 := h2145;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2699) := h40881;
    (Or.elim h20853 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (u6 q4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step48331 (p2000 p2409 p3452 p5193 : Prop)
    (h2160 : p2000)
    (h40874 : (¬ p2409))
    (h20857 : (¬ p2000) ∨ p2409 ∨ (¬ p3452) ∨ p5193)
    : (¬ p3452) ∨ p5193 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3452 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5193) := (fun h => hn (Or.inr h));
    let u2 : p2000 := h2160;
    let u3 : (¬ p2409) := h40874;
    (Or.elim h20857 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (u1 r2)))))))))

theorem step48332 (p2027 p2396 p2761 p4473 p5228 p5387 : Prop)
    (h40810 : (¬ p2027))
    (h20858 : p2027 ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p5387))
    : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4473) ∨ (¬ p5228) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4473 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20858 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step48333 (p1995 p2027 p2499 p2766 p3266 p4137 p4191 : Prop)
    (h2155 : p1995)
    (h40810 : (¬ p2027))
    (h40884 : (¬ p2766))
    (h20859 : (¬ p1995) ∨ p2027 ∨ (¬ p2499) ∨ p2766 ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191))
    : (¬ p2499) ∨ (¬ p3266) ∨ (¬ p4137) ∨ (¬ p4191) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2499 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4137 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4191 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p1995 := h2155;
    let u5 : (¬ p2027) := h40810;
    let u6 : (¬ p2766) := h40884;
    (Or.elim h20859 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u5 q1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (u6 q3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step48334 (p2027 p2707 p3585 p3658 p3742 p4753 : Prop)
    (h40810 : (¬ p2027))
    (h20860 : p2027 ∨ (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3742) ∨ (¬ p4753))
    : (¬ p2707) ∨ (¬ p3585) ∨ (¬ p3658) ∨ (¬ p3742) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3585 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3658 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : (¬ p2027) := h40810;
    (Or.elim h20860 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

end ElevenRUP
