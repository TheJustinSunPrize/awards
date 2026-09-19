import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step95883 (p2187 p2274 p3097 p3527 p3548 p3550 p5142 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73404 : p3548 ∨ p3527)
    (h40977 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p5142))
    : (¬ p5142) ∨ (¬ p3550) ∨ p2274 ∨ (¬ p2187) ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5142 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40977 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95884 (p2295 p2668 p3527 p3548 p3550 p3568 p5142 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73404 : p3548 ∨ p3527)
    (h40974 : (¬ p2668) ∨ (¬ p3548) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p5142))
    : (¬ p2668) ∨ p2295 ∨ (¬ p3550) ∨ p3527 ∨ (¬ p5142) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5142 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h40974 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95885 (p2417 p2901 p3115 p4208 p4209 p4647 p5295 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h57771 : (¬ p2417) ∨ (¬ p2901) ∨ (¬ p4208) ∨ (¬ p4209) ∨ (¬ p4647) ∨ (¬ p5295))
    : p3115 ∨ (¬ p4209) ∨ (¬ p2417) ∨ (¬ p5295) ∨ (¬ p4647) ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57771 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95887 (p2951 p3115 p4207 p4208 p4209 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h6304 : (¬ p2951) ∨ (¬ p4207) ∨ (¬ p4208) ∨ (¬ p4209))
    : p3115 ∨ (¬ p2951) ∨ (¬ p4207) ∨ (¬ p4209) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p2951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4209 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6304 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step95895 (p2252 p2608 p2750 p2946 p2952 p3146 p3156 p3440 p3497 p3692 p3830 p3954 p4181 p5122 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73498 : p3954 ∨ p2608)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h55202 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3440) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3830) ∨ (¬ p3954) ∨ (¬ p4181) ∨ (¬ p5122))
    : (¬ p4181) ∨ p3146 ∨ (¬ p3440) ∨ p2608 ∨ p3156 ∨ (¬ p2750) ∨ (¬ p5122) ∨ p2946 ∨ (¬ p2252) ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55202 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step95896 (p2295 p2307 p2651 p2657 p3568 p3987 p4975 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73288 : p2657 ∨ p2651)
    (h49439 : (¬ p2307) ∨ (¬ p2657) ∨ (¬ p3568) ∨ (¬ p3987) ∨ (¬ p4975))
    : (¬ p3987) ∨ (¬ p2307) ∨ (¬ p4975) ∨ p2295 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3987 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49439 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95897 (p2230 p2331 p2440 p2542 p2589 p2655 p4975 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h41379 : (¬ p2331) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4975))
    : (¬ p2331) ∨ p2440 ∨ (¬ p2655) ∨ (¬ p4975) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41379 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95899 (p2727 p4281 p5912 : Prop)
    (h74223 : (¬ p2727) ∨ (¬ p5912))
    (h12454 : p4281 ∨ p5912)
    : p4281 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4281) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5912) := (Or.elim h74223 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12454 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95900 (p2727 p3487 p5912 : Prop)
    (h74223 : (¬ p2727) ∨ (¬ p5912))
    (h12455 : p3487 ∨ p5912)
    : p3487 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3487) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5912) := (Or.elim h74223 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12455 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95901 (p2727 p4813 p5912 : Prop)
    (h74223 : (¬ p2727) ∨ (¬ p5912))
    (h12457 : p4813 ∨ p5912)
    : p4813 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4813) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5912) := (Or.elim h74223 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12457 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95903 (p2177 p2299 p2396 p2437 p3516 p3742 p3821 p4279 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73452 : p3742 ∨ p2437)
    (h73234 : p2299 ∨ p2177)
    (h45139 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p3742) ∨ (¬ p3821) ∨ (¬ p4279))
    : (¬ p2396) ∨ p3516 ∨ p2437 ∨ (¬ p4279) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45139 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95904 (p2396 p2437 p3083 p3543 p3742 p4107 p4279 p4404 p4427 p4666 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73452 : p3742 ∨ p2437)
    (h42537 : (¬ p3083) ∨ (¬ p3543) ∨ (¬ p3742) ∨ (¬ p4107) ∨ (¬ p4279) ∨ (¬ p4404) ∨ (¬ p4427) ∨ (¬ p4666))
    : (¬ p4279) ∨ (¬ p3083) ∨ p2396 ∨ p2437 ∨ (¬ p3543) ∨ (¬ p4666) ∨ (¬ p4427) ∨ (¬ p4404) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4279 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4404 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42537 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step95905 (p2417 p3516 p3821 p4278 p4279 : Prop)
    (h73545 : (¬ p2417) ∨ (¬ p4278))
    (h73470 : p3821 ∨ p3516)
    (h36433 : (¬ p3821) ∨ p4278 ∨ (¬ p4279))
    : (¬ p2417) ∨ p3516 ∨ (¬ p4279) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3516) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4278) := (Or.elim h73545 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h36433 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step95906 (p2341 p2911 p3551 p3644 p4279 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73433 : (¬ p2911) ∨ (¬ p3644))
    (h15109 : (¬ p3551) ∨ p3644 ∨ (¬ p4279))
    : (¬ p4279) ∨ p2341 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4279 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2341) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3644) := (Or.elim h73433 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h15109 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step95914 (p2449 p2922 p2928 p3516 p3580 p3821 p4279 p4811 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73320 : p2928 ∨ p2922)
    (h41135 : (¬ p2449) ∨ (¬ p2928) ∨ (¬ p3580) ∨ (¬ p3821) ∨ (¬ p4279) ∨ (¬ p4811))
    : p3516 ∨ (¬ p2449) ∨ (¬ p3580) ∨ (¬ p4279) ∨ (¬ p4811) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41135 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step95923 (p3399 p5206 p6043 : Prop)
    (h74381 : p3399 ∨ (¬ p6043))
    (h13253 : p5206 ∨ p6043)
    : p5206 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5206) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6043) := (Or.elim h74381 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13253 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95924 (p3399 p3543 p6043 : Prop)
    (h74381 : p3399 ∨ (¬ p6043))
    (h13254 : p3543 ∨ p6043)
    : p3543 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3543) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6043) := (Or.elim h74381 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13254 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95927 (p2088 p2578 p2870 p3073 p3096 p4114 p4261 p4359 p4558 p5315 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h50995 : (¬ p2088) ∨ (¬ p2578) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4114) ∨ (¬ p4261) ∨ (¬ p4359) ∨ (¬ p4558) ∨ (¬ p5315))
    : (¬ p4114) ∨ (¬ p5315) ∨ (¬ p2088) ∨ (¬ p2578) ∨ p3073 ∨ (¬ p4558) ∨ (¬ p2870) ∨ (¬ p3096) ∨ (¬ p4359) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5315 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3073) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4359 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50995 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step95928 (p2528 p2534 p2608 p3449 p3609 p3954 p5315 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73268 : p2534 ∨ p2528)
    (h65262 : (¬ p2534) ∨ (¬ p3449) ∨ (¬ p3609) ∨ (¬ p3954) ∨ (¬ p5315))
    : (¬ p5315) ∨ (¬ p3609) ∨ p2608 ∨ (¬ p3449) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5315 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h65262 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95932 (p2274 p2307 p2313 p2787 p3125 p3276 p3286 p3670 p3744 p4117 p4425 p5322 p5454 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73454 : p3744 ∨ p3125)
    (h73238 : p2313 ∨ p2307)
    (h48980 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2787) ∨ (¬ p3286) ∨ (¬ p3670) ∨ (¬ p3744) ∨ (¬ p4117) ∨ (¬ p4425) ∨ (¬ p5322) ∨ (¬ p5454))
    : p3276 ∨ (¬ p3670) ∨ p3125 ∨ (¬ p4117) ∨ (¬ p2787) ∨ (¬ p5454) ∨ (¬ p2274) ∨ p2307 ∨ (¬ p3286) ∨ (¬ p5322) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48980 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step95934 (p3449 p4416 p6055 : Prop)
    (h74397 : p3449 ∨ (¬ p6055))
    (h13333 : p4416 ∨ p6055)
    : p4416 ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4416) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6055) := (Or.elim h74397 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13333 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95935 (p3449 p5239 p6055 : Prop)
    (h74397 : p3449 ∨ (¬ p6055))
    (h13334 : p5239 ∨ p6055)
    : p5239 ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5239) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6055) := (Or.elim h74397 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13334 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95936 (p3439 p3449 p6055 : Prop)
    (h74397 : p3449 ∨ (¬ p6055))
    (h13336 : p3439 ∨ p6055)
    : p3439 ∨ p3449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3439) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3449) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6055) := (Or.elim h74397 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13336 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95937 (p2341 p2911 p2936 p3516 p3631 p3644 p3821 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h73434 : p3644 ∨ p2911)
    (h48785 : (¬ p2341) ∨ (¬ p2936) ∨ (¬ p3631) ∨ (¬ p3644) ∨ (¬ p3821))
    : p3516 ∨ (¬ p3631) ∨ (¬ p2936) ∨ (¬ p2341) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2936 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48785 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step95942 (p2284 p3276 p3506 p3952 p4425 p4952 p5038 p5046 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73496 : p3952 ∨ p2284)
    (h50576 : (¬ p3506) ∨ (¬ p3952) ∨ (¬ p4425) ∨ (¬ p4952) ∨ (¬ p5038) ∨ (¬ p5046))
    : p3276 ∨ (¬ p5038) ∨ p2284 ∨ (¬ p5046) ∨ (¬ p3506) ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50576 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95943 (p2982 p3506 p4322 p4705 p4948 p5038 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h41828 : (¬ p3506) ∨ (¬ p4322) ∨ (¬ p4705) ∨ (¬ p4948) ∨ (¬ p5038))
    : (¬ p4322) ∨ (¬ p5038) ∨ (¬ p3506) ∨ (¬ p4705) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5038 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41828 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95944 (p2341 p2881 p2901 p2954 p3551 p4984 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h41823 : (¬ p2881) ∨ (¬ p2901) ∨ (¬ p2954) ∨ (¬ p3551) ∨ (¬ p4984))
    : (¬ p2954) ∨ (¬ p4984) ∨ p2341 ∨ (¬ p2901) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2954 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41823 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95947 (p2187 p2284 p2383 p2387 p2954 p4198 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h52291 : (¬ p2187) ∨ (¬ p2284) ∨ (¬ p2387) ∨ (¬ p2954) ∨ (¬ p4198))
    : (¬ p2187) ∨ p2383 ∨ (¬ p4198) ∨ (¬ p2954) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2954 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h52291 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95954 (p2396 p2707 p3588 p3599 p4107 p4477 p5233 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73514 : p4107 ∨ p2396)
    (h41286 : (¬ p3588) ∨ (¬ p3599) ∨ (¬ p4107) ∨ (¬ p4477) ∨ (¬ p5233))
    : (¬ p3599) ∨ (¬ p5233) ∨ p2707 ∨ p2396 ∨ (¬ p4477) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41286 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step95958 (p2143 p2427 p2696 p2829 p2982 p3051 p3365 p3366 p3483 p3556 p4368 p4948 p5052 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73846 : p4948 ∨ p2982)
    (h73390 : p3365 ∨ p2696)
    (h51294 : (¬ p2143) ∨ (¬ p2427) ∨ (¬ p2829) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3483) ∨ (¬ p3556) ∨ (¬ p4368) ∨ (¬ p4948) ∨ (¬ p5052))
    : p3051 ∨ (¬ p2427) ∨ (¬ p2829) ∨ (¬ p3483) ∨ p2982 ∨ (¬ p3366) ∨ (¬ p2143) ∨ (¬ p5052) ∨ p2696 ∨ (¬ p4368) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2143 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5052 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51294 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step95959 (p2341 p2437 p3083 p4256 p4383 p5203 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h41713 : (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4256) ∨ (¬ p4383) ∨ (¬ p5203))
    : p3083 ∨ (¬ p2341) ∨ (¬ p2437) ∨ (¬ p4383) ∨ (¬ p5203) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41713 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step95961 (p2307 p2313 p2505 p2850 p3309 p3684 p4031 p4198 p5217 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73442 : p3684 ∨ p2850)
    (h50764 : (¬ p2313) ∨ (¬ p2505) ∨ (¬ p3309) ∨ (¬ p3684) ∨ (¬ p4031) ∨ (¬ p4198) ∨ (¬ p5217))
    : (¬ p3309) ∨ p2307 ∨ (¬ p4031) ∨ (¬ p5217) ∨ (¬ p2505) ∨ (¬ p4198) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2505 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50764 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step95963 (p2274 p4140 p5819 : Prop)
    (h74103 : (¬ p2274) ∨ (¬ p5819))
    (h11911 : p4140 ∨ p5819)
    : p4140 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4140) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5819) := (Or.elim h74103 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11911 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95964 (p2274 p3872 p5819 : Prop)
    (h74103 : (¬ p2274) ∨ (¬ p5819))
    (h11912 : p3872 ∨ p5819)
    : p3872 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3872) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5819) := (Or.elim h74103 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11912 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95967 (p2470 p2476 p2717 p3389 p4383 p5087 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h63663 : (¬ p2476) ∨ (¬ p2717) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p5087))
    : (¬ p5087) ∨ (¬ p2717) ∨ (¬ p4383) ∨ (¬ p3389) ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5087 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63663 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step95968 (p2437 p2481 p2717 p3083 p3960 p4256 p5087 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h49132 : (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2717) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p5087))
    : (¬ p2481) ∨ (¬ p3960) ∨ (¬ p2437) ∨ p3083 ∨ (¬ p2717) ∨ (¬ p5087) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5087 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49132 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step95970 (p2807 p3286 p3292 p4661 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h19994 : (¬ p2807) ∨ (¬ p3292) ∨ (¬ p4661))
    : p3286 ∨ (¬ p4661) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p4661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19994 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step95973 (p2396 p2553 p2573 p2696 p3005 p3256 p3365 p3877 p3950 p4118 p4419 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h64683 : (¬ p2396) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3365) ∨ (¬ p3877) ∨ (¬ p3950) ∨ (¬ p4118) ∨ (¬ p4419))
    : p3256 ∨ p3005 ∨ (¬ p2573) ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p2553) ∨ p2696 ∨ (¬ p4419) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64683 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step95974 (p2417 p2696 p2761 p3005 p3365 p3389 p3877 p4419 p5123 p5600 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73390 : p3365 ∨ p2696)
    (h64902 : (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p3389) ∨ (¬ p3877) ∨ (¬ p4419) ∨ (¬ p5123) ∨ (¬ p5600))
    : (¬ p5600) ∨ p3005 ∨ (¬ p4419) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p5123) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5600 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64902 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95975 (p2553 p2573 p3166 p3172 p3256 p3266 p3791 p4118 p4236 p4419 p4444 p4826 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h73520 : p4118 ∨ p3256)
    (h73580 : p4444 ∨ p3266)
    (h62627 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3172) ∨ (¬ p3791) ∨ (¬ p4118) ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p4444) ∨ (¬ p4826))
    : p3166 ∨ p3256 ∨ (¬ p4826) ∨ p3266 ∨ (¬ p2573) ∨ (¬ p4236) ∨ (¬ p3791) ∨ (¬ p4419) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62627 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step95976 (p3005 p4967 p5963 : Prop)
    (h74291 : (¬ p3005) ∨ (¬ p5963))
    (h12765 : p4967 ∨ p5963)
    : p4967 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4967) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5963) := (Or.elim h74291 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12765 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95977 (p3005 p4373 p5963 : Prop)
    (h74291 : (¬ p3005) ∨ (¬ p5963))
    (h12766 : p4373 ∨ p5963)
    : p4373 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4373) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5963) := (Or.elim h74291 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12766 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95978 (p3005 p4968 p5963 : Prop)
    (h74291 : (¬ p3005) ∨ (¬ p5963))
    (h12768 : p4968 ∨ p5963)
    : p4968 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4968) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5963) := (Or.elim h74291 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12768 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95979 (p3005 p4969 p5963 : Prop)
    (h74291 : (¬ p3005) ∨ (¬ p5963))
    (h12769 : p4969 ∨ p5963)
    : p4969 ∨ (¬ p3005) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4969) := (fun h => hn (Or.inl h));
    let u1 : p3005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5963) := (Or.elim h74291 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12769 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95980 (p2341 p2911 p3346 p3644 p4637 p5201 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h52653 : (¬ p2341) ∨ (¬ p3346) ∨ (¬ p3644) ∨ (¬ p4637) ∨ (¬ p5201))
    : (¬ p4637) ∨ (¬ p2341) ∨ (¬ p5201) ∨ (¬ p3346) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4637 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52653 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step95981 (p2598 p3905 p5881 : Prop)
    (h74181 : p2598 ∨ (¬ p5881))
    (h12274 : p3905 ∨ p5881)
    : p3905 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3905) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5881) := (Or.elim h74181 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12274 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95982 (p2598 p4419 p5881 : Prop)
    (h74181 : p2598 ∨ (¬ p5881))
    (h12275 : p4419 ∨ p5881)
    : p4419 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4419) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5881) := (Or.elim h74181 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12275 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95983 (p2598 p3759 p5881 : Prop)
    (h74181 : p2598 ∨ (¬ p5881))
    (h12278 : p3759 ∨ p5881)
    : p3759 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3759) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5881) := (Or.elim h74181 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12278 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95984 (p2241 p2247 p2363 p2383 p2459 p2727 p3083 p4111 p4256 p4348 p4438 p5017 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73518 : p4111 ∨ p2727)
    (h73542 : p4256 ∨ p3083)
    (h73226 : p2247 ∨ p2241)
    (h55495 : (¬ p2247) ∨ (¬ p2363) ∨ (¬ p2383) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p5017))
    : (¬ p5017) ∨ (¬ p2383) ∨ (¬ p2363) ∨ p2459 ∨ p2727 ∨ p3083 ∨ p2241 ∨ (¬ p4438) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5017 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55495 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95985 (p2241 p2247 p2307 p2459 p2727 p2881 p3343 p3359 p4111 p4275 p4697 p5017 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h73388 : p3359 ∨ p3343)
    (h41994 : (¬ p2247) ∨ (¬ p2307) ∨ (¬ p2459) ∨ (¬ p2881) ∨ (¬ p3359) ∨ (¬ p4111) ∨ (¬ p4275) ∨ (¬ p4697) ∨ (¬ p5017))
    : (¬ p2307) ∨ (¬ p2881) ∨ (¬ p2459) ∨ p2727 ∨ (¬ p4275) ∨ p2241 ∨ (¬ p5017) ∨ (¬ p4697) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41994 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step95986 (p2241 p2247 p2284 p2992 p3662 p3952 p4356 p5017 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73226 : p2247 ∨ p2241)
    (h73496 : p3952 ∨ p2284)
    (h41957 : (¬ p2247) ∨ (¬ p3662) ∨ (¬ p3952) ∨ (¬ p4356) ∨ (¬ p5017))
    : p2992 ∨ p2241 ∨ (¬ p4356) ∨ (¬ p5017) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5017 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41957 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step95989 (p2187 p2241 p2247 p2274 p2307 p2727 p3083 p3097 p4111 p4256 p4384 p5017 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73352 : p3097 ∨ p2274)
    (h73226 : p2247 ∨ p2241)
    (h73518 : p4111 ∨ p2727)
    (h41993 : (¬ p2187) ∨ (¬ p2247) ∨ (¬ p2307) ∨ (¬ p3097) ∨ (¬ p4111) ∨ (¬ p4256) ∨ (¬ p4384) ∨ (¬ p5017))
    : (¬ p5017) ∨ (¬ p2187) ∨ p3083 ∨ (¬ p2307) ∨ p2274 ∨ p2241 ∨ p2727 ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5017 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h41993 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step95992 (p2363 p3115 p3156 p3497 p4134 p4347 p4695 p4947 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73400 : p3497 ∨ p3156)
    (h56466 : (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4695) ∨ (¬ p4947))
    : p2363 ∨ (¬ p4695) ∨ p3156 ∨ (¬ p4947) ∨ (¬ p4134) ∨ (¬ p3115) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56466 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step95997 (p2982 p4449 p5957 : Prop)
    (h74283 : (¬ p2982) ∨ (¬ p5957))
    (h12726 : p4449 ∨ p5957)
    : p4449 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4449) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5957) := (Or.elim h74283 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12726 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step95998 (p2651 p2657 p3286 p3292 p5170 : Prop)
    (h73377 : (¬ p3286) ∨ (¬ p3292))
    (h73288 : p2657 ∨ p2651)
    (h27055 : (¬ p2657) ∨ p3292 ∨ (¬ p5170))
    : (¬ p3286) ∨ (¬ p5170) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3286 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3292) := (Or.elim h73377 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h27055 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96001 (p2331 p2651 p2657 p4421 p5170 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h19880 : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p4421) ∨ (¬ p5170))
    : (¬ p4421) ∨ (¬ p2331) ∨ p2651 ∨ (¬ p5170) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4421 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19880 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step96004 (p2528 p4695 p5870 : Prop)
    (h74167 : (¬ p2528) ∨ (¬ p5870))
    (h12211 : p4695 ∨ p5870)
    : p4695 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4695) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5870) := (Or.elim h74167 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12211 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96005 (p2528 p3358 p5870 : Prop)
    (h74167 : (¬ p2528) ∨ (¬ p5870))
    (h12212 : p3358 ∨ p5870)
    : p3358 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3358) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5870) := (Or.elim h74167 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12212 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96007 (p2528 p4697 p5870 : Prop)
    (h74167 : (¬ p2528) ∨ (¬ p5870))
    (h12215 : p4697 ∨ p5870)
    : p4697 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4697) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5870) := (Or.elim h74167 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12215 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96012 (p2501 p2553 p3093 p3399 p4366 p4427 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h41399 : (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) ∨ (¬ p4366) ∨ (¬ p4427))
    : p3399 ∨ (¬ p4427) ∨ (¬ p2501) ∨ (¬ p2553) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p4427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41399 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96016 (p2230 p4031 p5813 : Prop)
    (h74095 : (¬ p2230) ∨ (¬ p5813))
    (h11878 : p4031 ∨ p5813)
    : p4031 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4031) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5813) := (Or.elim h74095 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11878 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96017 (p2230 p4399 p5813 : Prop)
    (h74095 : (¬ p2230) ∨ (¬ p5813))
    (h11880 : p4399 ∨ p5813)
    : p4399 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4399) := (fun h => hn (Or.inl h));
    let u1 : p2230 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5813) := (Or.elim h74095 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11880 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96019 (p2177 p2210 p2299 p2319 p2341 p2396 p2608 p2972 p3555 p3951 p4363 p4866 p5016 : Prop)
    (h73568 : p4363 ∨ p2972)
    (h73412 : p3555 ∨ p2210)
    (h73234 : p2299 ∨ p2177)
    (h58696 : (¬ p2299) ∨ (¬ p2319) ∨ (¬ p2341) ∨ (¬ p2396) ∨ (¬ p2608) ∨ (¬ p3555) ∨ (¬ p3951) ∨ (¬ p4363) ∨ (¬ p4866) ∨ (¬ p5016))
    : (¬ p2608) ∨ (¬ p2319) ∨ (¬ p2396) ∨ (¬ p2341) ∨ (¬ p4866) ∨ p2972 ∨ p2210 ∨ p2177 ∨ (¬ p5016) ∨ (¬ p3951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58696 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step96020 (p2641 p4760 p5894 : Prop)
    (h74199 : (¬ p2641) ∨ (¬ p5894))
    (h12350 : p4760 ∨ p5894)
    : p4760 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4760) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5894) := (Or.elim h74199 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12350 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96021 (p2641 p3922 p5894 : Prop)
    (h74199 : (¬ p2641) ∨ (¬ p5894))
    (h12351 : p3922 ∨ p5894)
    : p3922 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3922) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5894) := (Or.elim h74199 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12351 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96022 (p2641 p4759 p5894 : Prop)
    (h74199 : (¬ p2641) ∨ (¬ p5894))
    (h12352 : p4759 ∨ p5894)
    : p4759 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4759) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5894) := (Or.elim h74199 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12352 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96024 (p3016 p4389 p5965 : Prop)
    (h74293 : p3016 ∨ (¬ p5965))
    (h12779 : p4389 ∨ p5965)
    : p4389 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4389) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5965) := (Or.elim h74293 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12779 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96025 (p3016 p4194 p5965 : Prop)
    (h74293 : p3016 ∨ (¬ p5965))
    (h12781 : p4194 ∨ p5965)
    : p4194 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4194) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5965) := (Or.elim h74293 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12781 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96026 (p3016 p4972 p5965 : Prop)
    (h74293 : p3016 ∨ (¬ p5965))
    (h12782 : p4972 ∨ p5965)
    : p4972 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4972) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5965) := (Or.elim h74293 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12782 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96028 (p2307 p2313 p2352 p2553 p2696 p2753 p3136 p3156 p3204 p3956 p4433 p4870 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73238 : p2313 ∨ p2307)
    (h64179 : (¬ p2313) ∨ (¬ p2553) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3136) ∨ (¬ p3156) ∨ (¬ p3204) ∨ (¬ p3956) ∨ (¬ p4433) ∨ (¬ p4870))
    : (¬ p2753) ∨ (¬ p3204) ∨ (¬ p2553) ∨ (¬ p4870) ∨ p2352 ∨ (¬ p3156) ∨ (¬ p3136) ∨ p2307 ∨ (¬ p4433) ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64179 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step96029 (p2696 p2737 p3093 p3365 p3873 p4870 : Prop)
    (h73390 : p3365 ∨ p2696)
    (h42483 : (¬ p2737) ∨ (¬ p3093) ∨ (¬ p3365) ∨ (¬ p3873) ∨ (¬ p4870))
    : p2696 ∨ (¬ p3093) ∨ (¬ p4870) ∨ (¬ p3873) ∨ (¬ p2737) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3873 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42483 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96032 (p2761 p3276 p4381 p4425 p4636 : Prop)
    (h73577 : (¬ p3276) ∨ (¬ p4425))
    (h73574 : p4381 ∨ p2761)
    (h23986 : (¬ p4381) ∨ p4425 ∨ (¬ p4636))
    : (¬ p3276) ∨ p2761 ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4425) := (Or.elim h73577 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h23986 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96033 (p2437 p2761 p2922 p2928 p3343 p3359 p3402 p4381 p4636 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73388 : p3359 ∨ p3343)
    (h73320 : p2928 ∨ p2922)
    (h63105 : (¬ p2437) ∨ (¬ p2928) ∨ (¬ p3359) ∨ (¬ p3402) ∨ (¬ p4381) ∨ (¬ p4636))
    : (¬ p3402) ∨ p2761 ∨ (¬ p2437) ∨ p3343 ∨ p2922 ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63105 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step96034 (p2396 p2437 p3343 p3359 p4276 p4636 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h59676 : (¬ p2396) ∨ (¬ p2437) ∨ (¬ p3359) ∨ (¬ p4276) ∨ (¬ p4636))
    : p3343 ∨ (¬ p4636) ∨ (¬ p2437) ∨ (¬ p2396) ∨ (¬ p4276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59676 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96042 (p2363 p3527 p3548 p3631 p4133 p4347 p4636 p4695 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73560 : p4347 ∨ p2363)
    (h53981 : (¬ p3548) ∨ (¬ p3631) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4636) ∨ (¬ p4695))
    : (¬ p3631) ∨ (¬ p4695) ∨ (¬ p4133) ∨ p3527 ∨ (¬ p4636) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53981 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96044 (p2685 p3032 p3266 p3276 p3516 p3543 p4444 p4636 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h61211 : (¬ p2685) ∨ (¬ p3032) ∨ (¬ p3276) ∨ (¬ p3516) ∨ (¬ p3543) ∨ (¬ p4444) ∨ (¬ p4636))
    : (¬ p3543) ∨ p3266 ∨ (¬ p3516) ∨ (¬ p3032) ∨ (¬ p2685) ∨ (¬ p3276) ∨ (¬ p4636) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3543 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3032 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61211 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step96045 (p2210 p2982 p3830 p3834 p4388 p4629 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h55633 : (¬ p2210) ∨ (¬ p2982) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p4629))
    : p3830 ∨ (¬ p4388) ∨ (¬ p2982) ∨ (¬ p4629) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4629 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55633 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96047 (p2210 p3115 p3830 p3834 p4388 p4957 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h42633 : (¬ p2210) ∨ (¬ p3115) ∨ (¬ p3834) ∨ (¬ p4388) ∨ (¬ p4957))
    : p3830 ∨ (¬ p3115) ∨ (¬ p4388) ∨ (¬ p2210) ∨ (¬ p4957) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4388 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42633 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96055 (p3105 p3680 p3707 p4321 p4875 p4938 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h48913 : (¬ p3105) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4875) ∨ (¬ p4938))
    : p3707 ∨ (¬ p3680) ∨ (¬ p3105) ∨ (¬ p4938) ∨ (¬ p4875) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48913 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96056 (p3115 p3680 p3707 p4321 p4938 p4957 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h41619 : (¬ p3115) ∨ (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4938) ∨ (¬ p4957))
    : (¬ p3115) ∨ p3707 ∨ (¬ p4957) ∨ (¬ p3680) ∨ (¬ p4938) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41619 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96057 (p2982 p3680 p3707 p4282 p4321 p4702 p4938 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h48101 : (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4282) ∨ (¬ p4321) ∨ (¬ p4702) ∨ (¬ p4938))
    : p3707 ∨ (¬ p4282) ∨ (¬ p4702) ∨ (¬ p3680) ∨ (¬ p2982) ∨ (¬ p4938) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4938 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48101 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step96058 (p2341 p2608 p3527 p3545 p3548 p3954 p4796 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73498 : p3954 ∨ p2608)
    (h49272 : (¬ p2341) ∨ (¬ p3545) ∨ (¬ p3548) ∨ (¬ p3954) ∨ (¬ p4796))
    : p3527 ∨ p2608 ∨ (¬ p3545) ∨ (¬ p4796) ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3545 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4796 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49272 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96060 (p3319 p5152 p6026 : Prop)
    (h74367 : (¬ p3319) ∨ (¬ p6026))
    (h13150 : p5152 ∨ p6026)
    : p5152 ∨ (¬ p3319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5152) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6026) := (Or.elim h74367 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13150 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96061 (p3319 p5153 p6026 : Prop)
    (h74367 : (¬ p3319) ∨ (¬ p6026))
    (h13151 : p5153 ∨ p6026)
    : p5153 ∨ (¬ p3319) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5153) := (fun h => hn (Or.inl h));
    let u1 : p3319 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6026) := (Or.elim h74367 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13151 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96066 (p2992 p2996 p3027 p3156 p3497 p3662 p4333 p4901 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73440 : p3662 ∨ p2992)
    (h73340 : p3027 ∨ p2996)
    (h60393 : (¬ p3027) ∨ (¬ p3497) ∨ (¬ p3662) ∨ (¬ p4333) ∨ (¬ p4901))
    : p3156 ∨ p2992 ∨ (¬ p4901) ∨ p2996 ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60393 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96071 (p2459 p2470 p2528 p2946 p2952 p3005 p3136 p3877 p4041 p4236 p4348 p4419 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73562 : p4348 ∨ p2459)
    (h73488 : p3877 ∨ p3005)
    (h64944 : (¬ p2470) ∨ (¬ p2528) ∨ (¬ p2952) ∨ (¬ p3136) ∨ (¬ p3877) ∨ (¬ p4041) ∨ (¬ p4236) ∨ (¬ p4348) ∨ (¬ p4419))
    : p2946 ∨ (¬ p4236) ∨ (¬ p4419) ∨ (¬ p2470) ∨ (¬ p2528) ∨ p2459 ∨ p3005 ∨ (¬ p4041) ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4041 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64944 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step96073 (p2608 p2707 p3379 p3452 p3590 p5086 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h48954 : (¬ p2608) ∨ (¬ p2707) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p5086))
    : (¬ p2707) ∨ p3379 ∨ (¬ p3590) ∨ (¬ p2608) ∨ (¬ p5086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5086 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48954 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96076 (p2437 p3740 p5857 : Prop)
    (h74153 : p2437 ∨ (¬ p5857))
    (h12134 : p3740 ∨ p5857)
    : p3740 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5857) := (Or.elim h74153 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12134 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96077 (p2437 p4112 p5857 : Prop)
    (h74153 : p2437 ∨ (¬ p5857))
    (h12136 : p4112 ∨ p5857)
    : p4112 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4112) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5857) := (Or.elim h74153 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12136 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96078 (p2437 p4650 p5857 : Prop)
    (h74153 : p2437 ∨ (¬ p5857))
    (h12137 : p4650 ∨ p5857)
    : p4650 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4650) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5857) := (Or.elim h74153 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12137 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96081 (p2210 p2241 p2307 p2396 p2761 p3412 p3555 p4756 p5016 p5405 p5740 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h48257 : (¬ p2241) ∨ (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3412) ∨ (¬ p3555) ∨ (¬ p4756) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p5740) ∨ (¬ p2761) ∨ p2210 ∨ (¬ p2396) ∨ (¬ p2241) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p4756) ∨ (¬ p3412) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5740 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4756 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48257 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step96085 (p2363 p2383 p2696 p3136 p3266 p3365 p3366 p4315 p4866 p5016 p5405 p5740 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73390 : p3365 ∨ p2696)
    (h48222 : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p3266) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p4315) ∨ (¬ p4866) ∨ (¬ p5016) ∨ (¬ p5405) ∨ (¬ p5740))
    : (¬ p5016) ∨ (¬ p3266) ∨ (¬ p2383) ∨ (¬ p5405) ∨ (¬ p2363) ∨ (¬ p3366) ∨ (¬ p5740) ∨ (¬ p4866) ∨ p3136 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5740 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4866 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h48222 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step96086 (p2122 p2307 p3717 p3743 p3822 p4193 p5449 : Prop)
    (h73472 : p3822 ∨ p2122)
    (h53512 : (¬ p2307) ∨ (¬ p3717) ∨ (¬ p3743) ∨ (¬ p3822) ∨ (¬ p4193) ∨ (¬ p5449))
    : (¬ p3717) ∨ (¬ p5449) ∨ p2122 ∨ (¬ p2307) ∨ (¬ p3743) ∨ (¬ p4193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53512 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96087 (p2797 p3136 p3745 p4195 p4272 p5449 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h41931 : (¬ p3136) ∨ (¬ p3745) ∨ (¬ p4195) ∨ (¬ p4272) ∨ (¬ p5449))
    : (¬ p4272) ∨ (¬ p5449) ∨ (¬ p3136) ∨ (¬ p3745) ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4272 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2797) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41931 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96090 (p2363 p2383 p2598 p2781 p2850 p3055 p3266 p3684 p5405 p5433 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h41932 : (¬ p2363) ∨ (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3266) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433))
    : (¬ p5433) ∨ (¬ p5405) ∨ (¬ p2383) ∨ p2850 ∨ p2598 ∨ (¬ p3266) ∨ (¬ p2781) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5433 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41932 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step96092 (p3016 p3413 p3574 p4272 p4715 p5433 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h50740 : (¬ p3413) ∨ (¬ p3574) ∨ (¬ p4272) ∨ (¬ p4715) ∨ (¬ p5433))
    : (¬ p4272) ∨ (¬ p5433) ∨ p3016 ∨ (¬ p4715) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4272 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50740 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96093 (p2307 p2396 p2598 p2761 p2781 p2850 p3055 p3684 p5405 p5433 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73442 : p3684 ∨ p2850)
    (h55681 : (¬ p2307) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p5405) ∨ (¬ p5433))
    : (¬ p5433) ∨ (¬ p2307) ∨ (¬ p2781) ∨ p2598 ∨ (¬ p5405) ∨ (¬ p2396) ∨ (¬ p2761) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5433 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h55681 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step96096 (p3125 p3744 p4393 p4394 : Prop)
    (h73453 : (¬ p3125) ∨ (¬ p3744))
    (h6732 : p3744 ∨ (¬ p4393) ∨ (¬ p4394))
    : (¬ p4393) ∨ (¬ p4394) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4394 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3744) := (Or.elim h73453 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6732 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96097 (p2563 p2598 p2850 p3055 p3684 p4110 p4393 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73350 : p3055 ∨ p2598)
    (h73516 : p4110 ∨ p2563)
    (h45659 : (¬ p3055) ∨ (¬ p3684) ∨ (¬ p4110) ∨ (¬ p4393))
    : (¬ p4393) ∨ p2850 ∨ p2598 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45659 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96101 (p2132 p2138 p2417 p2761 p2860 p3389 p3758 p4393 p4419 p5254 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h64913 : (¬ p2138) ∨ (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3389) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4419) ∨ (¬ p5254))
    : (¬ p4393) ∨ p2132 ∨ (¬ p5254) ∨ (¬ p2417) ∨ (¬ p4419) ∨ (¬ p2761) ∨ (¬ p3389) ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64913 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step96103 (p2563 p3323 p3914 p4037 p4110 p4337 p4393 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73508 : p4037 ∨ p3323)
    (h46735 : (¬ p3914) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p4337) ∨ (¬ p4393))
    : (¬ p3914) ∨ (¬ p4393) ∨ (¬ p4337) ∨ p2563 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4337 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46735 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96107 (p2249 p2641 p2651 p2657 p3125 p3193 p3276 p3487 p4228 p4393 p4425 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73578 : p4425 ∨ p3276)
    (h52264 : (¬ p2249) ∨ (¬ p2641) ∨ (¬ p2657) ∨ (¬ p3125) ∨ (¬ p3193) ∨ (¬ p3487) ∨ (¬ p4228) ∨ (¬ p4393) ∨ (¬ p4425))
    : (¬ p4228) ∨ (¬ p4393) ∨ p2651 ∨ (¬ p3125) ∨ (¬ p2249) ∨ p3276 ∨ (¬ p3487) ∨ (¬ p2641) ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3276) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52264 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step96109 (p2192 p3156 p3497 p3747 p4173 p4228 p4336 p4393 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73400 : p3497 ∨ p3156)
    (h57625 : (¬ p3497) ∨ (¬ p3747) ∨ (¬ p4173) ∨ (¬ p4228) ∨ (¬ p4336) ∨ (¬ p4393))
    : (¬ p4228) ∨ (¬ p4393) ∨ (¬ p3747) ∨ p2192 ∨ p3156 ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57625 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96111 (p2156 p3051 p3646 p4140 p4393 p5472 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h42309 : (¬ p3051) ∨ (¬ p3646) ∨ (¬ p4140) ∨ (¬ p4393) ∨ (¬ p5472))
    : (¬ p4393) ∨ (¬ p4140) ∨ p2156 ∨ (¬ p3051) ∨ (¬ p5472) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42309 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96112 (p2192 p2210 p2761 p3425 p3434 p3471 p3555 p4173 p4393 p4733 p5254 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73412 : p3555 ∨ p2210)
    (h73396 : p3471 ∨ p3425)
    (h55627 : (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p3555) ∨ (¬ p4173) ∨ (¬ p4393) ∨ (¬ p4733) ∨ (¬ p5254))
    : (¬ p4393) ∨ (¬ p3434) ∨ p2192 ∨ p2210 ∨ p3425 ∨ (¬ p4733) ∨ (¬ p2761) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55627 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step96113 (p2252 p2284 p2608 p2750 p2946 p2952 p3707 p3830 p3952 p3954 p4393 p5254 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73330 : p2952 ∨ p2946)
    (h73498 : p3954 ∨ p2608)
    (h52034 : (¬ p2252) ∨ (¬ p2750) ∨ (¬ p2952) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p3952) ∨ (¬ p3954) ∨ (¬ p4393) ∨ (¬ p5254))
    : (¬ p4393) ∨ (¬ p3830) ∨ (¬ p5254) ∨ (¬ p3707) ∨ (¬ p2252) ∨ p2284 ∨ p2946 ∨ p2608 ∨ (¬ p2750) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52034 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step96114 (p2156 p2957 p3156 p3646 p3955 p4393 p4441 p5472 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h59897 : (¬ p2957) ∨ (¬ p3156) ∨ (¬ p3646) ∨ (¬ p3955) ∨ (¬ p4393) ∨ (¬ p4441) ∨ (¬ p5472))
    : (¬ p4393) ∨ (¬ p4441) ∨ (¬ p5472) ∨ (¬ p2957) ∨ p2156 ∨ (¬ p3156) ∨ (¬ p3955) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3955 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59897 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step96116 (p2156 p3156 p3497 p3646 p3747 p4228 p4336 p4393 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73400 : p3497 ∨ p3156)
    (h46667 : (¬ p3497) ∨ (¬ p3646) ∨ (¬ p3747) ∨ (¬ p4228) ∨ (¬ p4336) ∨ (¬ p4393))
    : (¬ p4228) ∨ (¬ p4393) ∨ p2156 ∨ p3156 ∨ (¬ p4336) ∨ (¬ p3747) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4393 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46667 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96117 (p2284 p2901 p3952 p4140 p4393 p5472 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h42427 : (¬ p2901) ∨ (¬ p3952) ∨ (¬ p4140) ∨ (¬ p4393) ∨ (¬ p5472))
    : (¬ p4393) ∨ (¬ p4140) ∨ (¬ p5472) ∨ p2284 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42427 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96120 (p2284 p2696 p3136 p3365 p3952 p4315 p4393 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73496 : p3952 ∨ p2284)
    (h73390 : p3365 ∨ p2696)
    (h61986 : (¬ p3365) ∨ (¬ p3952) ∨ (¬ p4315) ∨ (¬ p4393))
    : (¬ p4393) ∨ p3136 ∨ p2284 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61986 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96122 (p2132 p2138 p2449 p2761 p2807 p2860 p3758 p4393 p4786 p5254 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73456 : p3758 ∨ p2860)
    (h57482 : (¬ p2138) ∨ (¬ p2449) ∨ (¬ p2761) ∨ (¬ p2807) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4786) ∨ (¬ p5254))
    : (¬ p4393) ∨ p2132 ∨ p2860 ∨ (¬ p4786) ∨ (¬ p2807) ∨ (¬ p2761) ∨ (¬ p2449) ∨ (¬ p5254) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2132) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57482 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step96125 (p2132 p2138 p2860 p3166 p3256 p3266 p3758 p4393 p4786 p5254 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73214 : p2138 ∨ p2132)
    (h52119 : (¬ p2138) ∨ (¬ p3166) ∨ (¬ p3256) ∨ (¬ p3266) ∨ (¬ p3758) ∨ (¬ p4393) ∨ (¬ p4786) ∨ (¬ p5254))
    : (¬ p4393) ∨ (¬ p3166) ∨ p2860 ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p3256) ∨ (¬ p4786) ∨ p2132 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52119 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step96127 (p2860 p3758 p4053 p4338 p4393 p4878 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h50761 : (¬ p3758) ∨ (¬ p4053) ∨ (¬ p4338) ∨ (¬ p4393) ∨ (¬ p4878))
    : (¬ p4393) ∨ (¬ p4053) ∨ (¬ p4338) ∨ p2860 ∨ (¬ p4878) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4338 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4878 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50761 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96128 (p2284 p2341 p2459 p2946 p2952 p3266 p3952 p4393 p4850 p5248 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73496 : p3952 ∨ p2284)
    (h48028 : (¬ p2341) ∨ (¬ p2459) ∨ (¬ p2952) ∨ (¬ p3266) ∨ (¬ p3952) ∨ (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248))
    : (¬ p4393) ∨ (¬ p4850) ∨ (¬ p5248) ∨ p2946 ∨ (¬ p2341) ∨ p2284 ∨ (¬ p3266) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4393 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48028 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step96136 (p2307 p2313 p2396 p2598 p2753 p2761 p2850 p3204 p3727 p4107 p4381 p4870 p5400 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73514 : p4107 ∨ p2396)
    (h73238 : p2313 ∨ p2307)
    (h53944 : (¬ p2313) ∨ (¬ p2598) ∨ (¬ p2753) ∨ (¬ p2850) ∨ (¬ p3204) ∨ (¬ p3727) ∨ (¬ p4107) ∨ (¬ p4381) ∨ (¬ p4870) ∨ (¬ p5400))
    : p2761 ∨ (¬ p5400) ∨ (¬ p2598) ∨ (¬ p3204) ∨ p2396 ∨ (¬ p2850) ∨ (¬ p3727) ∨ p2307 ∨ (¬ p4870) ∨ (¬ p2753) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p5400 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53944 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u1)))))))))))))))))))))

theorem step96141 (p3564 p4331 p6083 : Prop)
    (h74427 : (¬ p3564) ∨ (¬ p6083))
    (h13549 : p4331 ∨ p6083)
    : p4331 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4331) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6083) := (Or.elim h74427 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13549 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96142 (p3564 p4422 p6083 : Prop)
    (h74427 : (¬ p3564) ∨ (¬ p6083))
    (h13550 : p4422 ∨ p6083)
    : p4422 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4422) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6083) := (Or.elim h74427 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13550 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96143 (p3564 p5324 p6083 : Prop)
    (h74427 : (¬ p3564) ∨ (¬ p6083))
    (h13552 : p5324 ∨ p6083)
    : p5324 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5324) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6083) := (Or.elim h74427 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13552 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96144 (p3564 p5325 p6083 : Prop)
    (h74427 : (¬ p3564) ∨ (¬ p6083))
    (h13553 : p5325 ∨ p6083)
    : p5325 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5325) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6083) := (Or.elim h74427 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13553 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96148 (p3801 p3811 p3816 : Prop)
    (h73465 : (¬ p3811) ∨ (¬ p3816))
    (h5625 : p3801 ∨ p3816)
    : p3801 ∨ (¬ p3811) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3801) := (fun h => hn (Or.inl h));
    let u1 : p3811 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3816) := (Or.elim h73465 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5625 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96149 (p2619 p4740 p5887 : Prop)
    (h74189 : p2619 ∨ (¬ p5887))
    (h12308 : p4740 ∨ p5887)
    : p4740 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4740) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5887) := (Or.elim h74189 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12308 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96150 (p2619 p4359 p5887 : Prop)
    (h74189 : p2619 ∨ (¬ p5887))
    (h12310 : p4359 ∨ p5887)
    : p4359 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4359) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5887) := (Or.elim h74189 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12310 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96151 (p2619 p4741 p5887 : Prop)
    (h74189 : p2619 ∨ (¬ p5887))
    (h12311 : p4741 ∨ p5887)
    : p4741 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4741) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5887) := (Or.elim h74189 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12311 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96152 (p2619 p4742 p5887 : Prop)
    (h74189 : p2619 ∨ (¬ p5887))
    (h12312 : p4742 ∨ p5887)
    : p4742 ∨ p2619 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4742) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2619) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5887) := (Or.elim h74189 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12312 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96153 (p3276 p4322 p4425 p4952 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h34954 : p4322 ∨ (¬ p4425) ∨ (¬ p4952))
    : p3276 ∨ p4322 ∨ (¬ p4952) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4322) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h34954 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96154 (p2230 p2427 p2589 p3193 p3222 p3347 p4235 p4952 p5104 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73284 : p2589 ∨ p2230)
    (h73536 : p4235 ∨ p2427)
    (h51266 : (¬ p2589) ∨ (¬ p3222) ∨ (¬ p3347) ∨ (¬ p4235) ∨ (¬ p4952) ∨ (¬ p5104))
    : p3193 ∨ (¬ p4952) ∨ p2230 ∨ (¬ p3347) ∨ p2427 ∨ (¬ p5104) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51266 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step96156 (p4149 p5670 p6175 : Prop)
    (h74465 : p4149 ∨ (¬ p6175))
    (h15080 : p5670 ∨ p6175)
    : p5670 ∨ p4149 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5670) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6175) := (Or.elim h74465 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h15080 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96163 (p2088 p2363 p3923 p4114 p4347 p5022 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h49413 : (¬ p2088) ∨ (¬ p3923) ∨ (¬ p4114) ∨ (¬ p4347) ∨ (¬ p5022))
    : (¬ p4114) ∨ p2363 ∨ (¬ p5022) ∨ (¬ p2088) ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4114 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5022 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49413 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96165 (p3425 p3820 p6061 : Prop)
    (h74405 : (¬ p3425) ∨ (¬ p6061))
    (h13373 : p3820 ∨ p6061)
    : p3820 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3820) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6061) := (Or.elim h74405 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13373 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96166 (p3425 p3577 p6061 : Prop)
    (h74405 : (¬ p3425) ∨ (¬ p6061))
    (h13374 : p3577 ∨ p6061)
    : p3577 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3577) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6061) := (Or.elim h74405 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13374 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96168 (p3425 p5258 p6061 : Prop)
    (h74405 : (¬ p3425) ∨ (¬ p6061))
    (h13377 : p5258 ∨ p6061)
    : p5258 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5258) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6061) := (Or.elim h74405 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13377 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96169 (p3246 p4135 p6011 : Prop)
    (h74347 : (¬ p3246) ∨ (¬ p6011))
    (h13059 : p4135 ∨ p6011)
    : p4135 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4135) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6011) := (Or.elim h74347 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13059 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96170 (p3246 p4192 p6011 : Prop)
    (h74347 : (¬ p3246) ∨ (¬ p6011))
    (h13060 : p4192 ∨ p6011)
    : p4192 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4192) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6011) := (Or.elim h74347 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13060 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96171 (p3246 p5104 p6011 : Prop)
    (h74347 : (¬ p3246) ∨ (¬ p6011))
    (h13062 : p5104 ∨ p6011)
    : p5104 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5104) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6011) := (Or.elim h74347 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13062 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96173 (p3434 p5233 p6053 : Prop)
    (h74395 : (¬ p3434) ∨ (¬ p6053))
    (h13316 : p5233 ∨ p6053)
    : p5233 ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5233) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6053) := (Or.elim h74395 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13316 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96174 (p3434 p5234 p6053 : Prop)
    (h74395 : (¬ p3434) ∨ (¬ p6053))
    (h13317 : p5234 ∨ p6053)
    : p5234 ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5234) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6053) := (Or.elim h74395 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13317 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96176 (p3434 p5236 p6053 : Prop)
    (h74395 : (¬ p3434) ∨ (¬ p6053))
    (h13320 : p5236 ∨ p6053)
    : p5236 ∨ (¬ p3434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5236) := (fun h => hn (Or.inl h));
    let u1 : p3434 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6053) := (Or.elim h74395 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13320 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96177 (p2341 p2396 p2881 p3276 p3286 p3551 p3670 p4107 p4117 p4275 p4425 p4638 p5260 p5454 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73514 : p4107 ∨ p2396)
    (h73408 : p3551 ∨ p2341)
    (h56151 : (¬ p2881) ∨ (¬ p3286) ∨ (¬ p3551) ∨ (¬ p3670) ∨ (¬ p4107) ∨ (¬ p4117) ∨ (¬ p4275) ∨ (¬ p4425) ∨ (¬ p4638) ∨ (¬ p5260) ∨ (¬ p5454))
    : p3276 ∨ p2396 ∨ (¬ p5260) ∨ (¬ p4275) ∨ (¬ p2881) ∨ (¬ p4638) ∨ (¬ p3670) ∨ (¬ p3286) ∨ (¬ p4117) ∨ (¬ p5454) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u13 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h56151 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u13))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step96180 (p2737 p2946 p2952 p3286 p3599 p4379 p5454 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h73330 : p2952 ∨ p2946)
    (h54998 : (¬ p2737) ∨ (¬ p2952) ∨ (¬ p3286) ∨ (¬ p4379) ∨ (¬ p5454))
    : p3599 ∨ (¬ p3286) ∨ (¬ p2737) ∨ (¬ p5454) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54998 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96183 (p3670 p5284 p5387 p5454 : Prop)
    (h74025 : (¬ p3670) ∨ (¬ p5387))
    (h37734 : (¬ p5284) ∨ p5387 ∨ (¬ p5454))
    : (¬ p3670) ∨ (¬ p5284) ∨ (¬ p5454) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5387) := (Or.elim h74025 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h37734 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96196 (p3461 p3564 p3670 p4137 p4191 p4421 p4976 p5454 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73524 : p4137 ∨ p3564)
    (h64326 : (¬ p3670) ∨ (¬ p4137) ∨ (¬ p4191) ∨ (¬ p4421) ∨ (¬ p4976) ∨ (¬ p5454))
    : (¬ p3670) ∨ p3461 ∨ (¬ p5454) ∨ (¬ p4976) ∨ p3564 ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5454 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64326 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step96197 (p3156 p4312 p5998 : Prop)
    (h74333 : p3156 ∨ (¬ p5998))
    (h12974 : p4312 ∨ p5998)
    : p4312 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4312) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5998) := (Or.elim h74333 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12974 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96198 (p3156 p3661 p5998 : Prop)
    (h74333 : p3156 ∨ (¬ p5998))
    (h12976 : p3661 ∨ p5998)
    : p3661 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3661) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5998) := (Or.elim h74333 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12976 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96199 (p3156 p5062 p5998 : Prop)
    (h74333 : p3156 ∨ (¬ p5998))
    (h12977 : p5062 ∨ p5998)
    : p5062 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5062) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5998) := (Or.elim h74333 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12977 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96209 (p2088 p2608 p3073 p3857 p4416 p5312 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h42229 : (¬ p2608) ∨ (¬ p3073) ∨ (¬ p3857) ∨ (¬ p4416) ∨ (¬ p5312))
    : (¬ p3073) ∨ p2088 ∨ (¬ p4416) ∨ (¬ p2608) ∨ (¬ p5312) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4416 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42229 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96214 (p3609 p4340 p4351 p4352 p4353 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h6614 : (¬ p4340) ∨ (¬ p4351) ∨ (¬ p4352) ∨ (¬ p4353))
    : (¬ p4353) ∨ p3609 ∨ (¬ p4352) ∨ (¬ p4351) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4353 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3609) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4351 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6614 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96219 (p3670 p4027 p6103 : Prop)
    (h74449 : p3670 ∨ (¬ p6103))
    (h13764 : p4027 ∨ p6103)
    : p4027 ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4027) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6103) := (Or.elim h74449 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13764 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96220 (p3670 p4028 p6103 : Prop)
    (h74449 : p3670 ∨ (¬ p6103))
    (h13766 : p4028 ∨ p6103)
    : p4028 ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4028) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6103) := (Or.elim h74449 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13766 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96223 (p2098 p2104 p3366 p3599 p4379 p5338 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h73571 : (¬ p3599) ∨ (¬ p4379))
    (h21819 : (¬ p2104) ∨ (¬ p3366) ∨ p4379 ∨ (¬ p5338))
    : (¬ p5338) ∨ p2098 ∨ (¬ p3366) ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5338 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2098) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3599 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : (¬ p4379) := (Or.elim h73571 (fun q0 => (False.elim (q0 u3))) (fun r0 => r0));
    (Or.elim h21819 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96225 (p2518 p2528 p3379 p3425 p3461 p3670 p4604 p4736 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h59322 : (¬ p2518) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p4736) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p2518) ∨ (¬ p4604) ∨ (¬ p5228) ∨ (¬ p4736) ∨ (¬ p2528) ∨ (¬ p3379) ∨ (¬ p3461) ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59322 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step96228 (p2220 p2761 p3115 p3156 p3366 p3370 p3425 p3497 p3670 p4377 p4395 p5228 p5387 : Prop)
    (h74026 : p5387 ∨ p3670)
    (h73400 : p3497 ∨ p3156)
    (h55926 : (¬ p2220) ∨ (¬ p2761) ∨ (¬ p3115) ∨ (¬ p3366) ∨ (¬ p3370) ∨ (¬ p3425) ∨ (¬ p3497) ∨ (¬ p4377) ∨ (¬ p4395) ∨ (¬ p5228) ∨ (¬ p5387))
    : p3670 ∨ (¬ p2761) ∨ (¬ p3366) ∨ (¬ p4395) ∨ (¬ p5228) ∨ (¬ p3115) ∨ p3156 ∨ (¬ p4377) ∨ (¬ p3425) ∨ (¬ p2220) ∨ (¬ p3370) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p5387 := (Or.elim h74026 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u12 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55926 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u11)))))))))))))))))))))))

theorem step96231 (p3830 p5486 p6127 : Prop)
    (h74461 : p3830 ∨ (¬ p6127))
    (h14006 : p5486 ∨ p6127)
    : p5486 ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5486) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6127) := (Or.elim h74461 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h14006 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96232 (p3830 p5487 p6127 : Prop)
    (h74461 : p3830 ∨ (¬ p6127))
    (h14007 : p5487 ∨ p6127)
    : p5487 ∨ p3830 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5487) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6127) := (Or.elim h74461 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h14007 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96234 (p3755 p5458 p6122 : Prop)
    (h74459 : (¬ p3755) ∨ (¬ p6122))
    (h13919 : p5458 ∨ p6122)
    : p5458 ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5458) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6122) := (Or.elim h74459 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13919 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96235 (p3755 p5459 p6122 : Prop)
    (h74459 : (¬ p3755) ∨ (¬ p6122))
    (h13920 : p5459 ∨ p6122)
    : p5459 ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5459) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6122) := (Or.elim h74459 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13920 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96236 (p3755 p5460 p6122 : Prop)
    (h74459 : (¬ p3755) ∨ (¬ p6122))
    (h13922 : p5460 ∨ p6122)
    : p5460 ∨ (¬ p3755) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5460) := (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6122) := (Or.elim h74459 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13922 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96243 (p3654 p4038 p6101 : Prop)
    (h74447 : (¬ p3654) ∨ (¬ p6101))
    (h13735 : p4038 ∨ p6101)
    : p4038 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4038) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6101) := (Or.elim h74447 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13735 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96244 (p3654 p4036 p6101 : Prop)
    (h74447 : (¬ p3654) ∨ (¬ p6101))
    (h13736 : p4036 ∨ p6101)
    : p4036 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4036) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6101) := (Or.elim h74447 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13736 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96246 (p3641 p5373 p6098 : Prop)
    (h74443 : (¬ p3641) ∨ (¬ p6098))
    (h13703 : p5373 ∨ p6098)
    : p5373 ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5373) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6098) := (Or.elim h74443 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13703 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96247 (p3641 p4354 p6098 : Prop)
    (h74443 : (¬ p3641) ∨ (¬ p6098))
    (h13704 : p4354 ∨ p6098)
    : (¬ p3641) ∨ p4354 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4354) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6098) := (Or.elim h74443 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h13704 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96249 (p3641 p5375 p6098 : Prop)
    (h74443 : (¬ p3641) ∨ (¬ p6098))
    (h13707 : p5375 ∨ p6098)
    : p5375 ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5375) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6098) := (Or.elim h74443 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13707 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96250 (p3631 p5362 p6095 : Prop)
    (h74439 : (¬ p3631) ∨ (¬ p6095))
    (h13673 : p5362 ∨ p6095)
    : p5362 ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5362) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6095) := (Or.elim h74439 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13673 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96251 (p3631 p5363 p6095 : Prop)
    (h74439 : (¬ p3631) ∨ (¬ p6095))
    (h13674 : p5363 ∨ p6095)
    : p5363 ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5363) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6095) := (Or.elim h74439 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13674 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96254 (p3609 p5343 p6089 : Prop)
    (h74435 : (¬ p3609) ∨ (¬ p6089))
    (h13638 : p5343 ∨ p6089)
    : p5343 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5343) := (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6089) := (Or.elim h74435 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13638 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96255 (p3609 p5344 p6089 : Prop)
    (h74435 : (¬ p3609) ∨ (¬ p6089))
    (h13639 : p5344 ∨ p6089)
    : p5344 ∨ (¬ p3609) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5344) := (fun h => hn (Or.inl h));
    let u1 : p3609 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6089) := (Or.elim h74435 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13639 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96260 (p3599 p5332 p6086 : Prop)
    (h74431 : (¬ p3599) ∨ (¬ p6086))
    (h13623 : p5332 ∨ p6086)
    : p5332 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5332) := (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6086) := (Or.elim h74431 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13623 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96261 (p3599 p5333 p6086 : Prop)
    (h74431 : (¬ p3599) ∨ (¬ p6086))
    (h13625 : p5333 ∨ p6086)
    : p5333 ∨ (¬ p3599) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5333) := (fun h => hn (Or.inl h));
    let u1 : p3599 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6086) := (Or.elim h74431 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13625 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96262 (p3537 p5317 p6080 : Prop)
    (h74423 : (¬ p3537) ∨ (¬ p6080))
    (h13509 : p5317 ∨ p6080)
    : p5317 ∨ (¬ p3537) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5317) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6080) := (Or.elim h74423 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13509 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96264 (p3537 p5315 p6080 : Prop)
    (h74423 : (¬ p3537) ∨ (¬ p6080))
    (h13511 : p5315 ∨ p6080)
    : p5315 ∨ (¬ p3537) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5315) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6080) := (Or.elim h74423 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13511 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96265 (p3537 p5316 p6080 : Prop)
    (h74423 : (¬ p3537) ∨ (¬ p6080))
    (h13512 : p5316 ∨ p6080)
    : p5316 ∨ (¬ p3537) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5316) := (fun h => hn (Or.inl h));
    let u1 : p3537 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6080) := (Or.elim h74423 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13512 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96266 (p3527 p5307 p6077 : Prop)
    (h74419 : (¬ p3527) ∨ (¬ p6077))
    (h13490 : p5307 ∨ p6077)
    : p5307 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5307) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6077) := (Or.elim h74419 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13490 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96267 (p3527 p4189 p6077 : Prop)
    (h74419 : (¬ p3527) ∨ (¬ p6077))
    (h13491 : p4189 ∨ p6077)
    : p4189 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4189) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6077) := (Or.elim h74419 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13491 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96270 (p3516 p5299 p6074 : Prop)
    (h74415 : (¬ p3516) ∨ (¬ p6074))
    (h13472 : p5299 ∨ p6074)
    : p5299 ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5299) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6074) := (Or.elim h74415 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13472 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96273 (p3516 p5300 p6074 : Prop)
    (h74415 : (¬ p3516) ∨ (¬ p6074))
    (h13475 : p5300 ∨ p6074)
    : p5300 ∨ (¬ p3516) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5300) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6074) := (Or.elim h74415 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13475 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96274 (p3422 p4390 p6050 : Prop)
    (h74391 : (¬ p3422) ∨ (¬ p6050))
    (h13296 : p4390 ∨ p6050)
    : p4390 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4390) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6050) := (Or.elim h74391 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13296 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96275 (p3422 p4375 p6050 : Prop)
    (h74391 : (¬ p3422) ∨ (¬ p6050))
    (h13297 : p4375 ∨ p6050)
    : p4375 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4375) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6050) := (Or.elim h74391 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13297 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96279 (p3389 p5201 p6041 : Prop)
    (h74379 : (¬ p3389) ∨ (¬ p6041))
    (h13243 : p5201 ∨ p6041)
    : p5201 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5201) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6041) := (Or.elim h74379 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13243 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96281 (p3389 p4279 p6041 : Prop)
    (h74379 : (¬ p3389) ∨ (¬ p6041))
    (h13246 : p4279 ∨ p6041)
    : p4279 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4279) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6041) := (Or.elim h74379 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13246 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96282 (p3343 p5171 p6031 : Prop)
    (h74369 : p3343 ∨ (¬ p6031))
    (h13179 : p5171 ∨ p6031)
    : p5171 ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5171) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6031) := (Or.elim h74369 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13179 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96283 (p3343 p5170 p6031 : Prop)
    (h74369 : p3343 ∨ (¬ p6031))
    (h13181 : p5170 ∨ p6031)
    : p5170 ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5170) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6031) := (Or.elim h74369 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13181 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96284 (p3343 p5172 p6031 : Prop)
    (h74369 : p3343 ∨ (¬ p6031))
    (h13182 : p5172 ∨ p6031)
    : p5172 ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5172) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6031) := (Or.elim h74369 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13182 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96286 (p3309 p3547 p6023 : Prop)
    (h74363 : (¬ p3309) ∨ (¬ p6023))
    (h13133 : p3547 ∨ p6023)
    : p3547 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3547) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6023) := (Or.elim h74363 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13133 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96287 (p3309 p4452 p6023 : Prop)
    (h74363 : (¬ p3309) ∨ (¬ p6023))
    (h13134 : p4452 ∨ p6023)
    : p4452 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4452) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6023) := (Or.elim h74363 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13134 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96289 (p3309 p5145 p6023 : Prop)
    (h74363 : (¬ p3309) ∨ (¬ p6023))
    (h13137 : p5145 ∨ p6023)
    : p5145 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5145) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6023) := (Or.elim h74363 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13137 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96290 (p3276 p5127 p6019 : Prop)
    (h74357 : p3276 ∨ (¬ p6019))
    (h13108 : p5127 ∨ p6019)
    : p5127 ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5127) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6019) := (Or.elim h74357 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13108 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96291 (p3276 p5126 p6019 : Prop)
    (h74357 : p3276 ∨ (¬ p6019))
    (h13110 : p5126 ∨ p6019)
    : p5126 ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5126) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6019) := (Or.elim h74357 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13110 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96293 (p3276 p5129 p6019 : Prop)
    (h74357 : p3276 ∨ (¬ p6019))
    (h13112 : p5129 ∨ p6019)
    : p5129 ∨ p3276 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5129) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6019) := (Or.elim h74357 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13112 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96294 (p3266 p5117 p6016 : Prop)
    (h74353 : p3266 ∨ (¬ p6016))
    (h13091 : p5117 ∨ p6016)
    : p5117 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5117) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6016) := (Or.elim h74353 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13091 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96295 (p3266 p5116 p6016 : Prop)
    (h74353 : p3266 ∨ (¬ p6016))
    (h13093 : p5116 ∨ p6016)
    : p5116 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5116) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6016) := (Or.elim h74353 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13093 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96297 (p3266 p5119 p6016 : Prop)
    (h74353 : p3266 ∨ (¬ p6016))
    (h13095 : p5119 ∨ p6016)
    : p5119 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5119) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr h));
    let u2 : (¬ p6016) := (Or.elim h74353 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h13095 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96298 (p3256 p4350 p6014 : Prop)
    (h74351 : (¬ p3256) ∨ (¬ p6014))
    (h13079 : p4350 ∨ p6014)
    : p4350 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4350) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6014) := (Or.elim h74351 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13079 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96299 (p3256 p5111 p6014 : Prop)
    (h74351 : (¬ p3256) ∨ (¬ p6014))
    (h13080 : p5111 ∨ p6014)
    : p5111 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5111) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6014) := (Or.elim h74351 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13080 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96302 (p3201 p3658 p6005 : Prop)
    (h74343 : (¬ p3201) ∨ (¬ p6005))
    (h13020 : p3658 ∨ p6005)
    : p3658 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3658) := (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6005) := (Or.elim h74343 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13020 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96303 (p3201 p5085 p6005 : Prop)
    (h74343 : (¬ p3201) ∨ (¬ p6005))
    (h13021 : p5085 ∨ p6005)
    : p5085 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5085) := (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6005) := (Or.elim h74343 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13021 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96304 (p3201 p5086 p6005 : Prop)
    (h74343 : (¬ p3201) ∨ (¬ p6005))
    (h13023 : p5086 ∨ p6005)
    : p5086 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5086) := (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6005) := (Or.elim h74343 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13023 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96305 (p3201 p5087 p6005 : Prop)
    (h74343 : (¬ p3201) ∨ (¬ p6005))
    (h13024 : p5087 ∨ p6005)
    : p5087 ∨ (¬ p3201) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5087) := (fun h => hn (Or.inl h));
    let u1 : p3201 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6005) := (Or.elim h74343 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13024 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96306 (p3189 p4288 p6002 : Prop)
    (h74339 : (¬ p3189) ∨ (¬ p6002))
    (h13000 : p4288 ∨ p6002)
    : p4288 ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4288) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6002) := (Or.elim h74339 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13000 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96307 (p3189 p3859 p6002 : Prop)
    (h74339 : (¬ p3189) ∨ (¬ p6002))
    (h13001 : p3859 ∨ p6002)
    : p3859 ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3859) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6002) := (Or.elim h74339 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13001 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96308 (p3189 p5078 p6002 : Prop)
    (h74339 : (¬ p3189) ∨ (¬ p6002))
    (h13003 : p5078 ∨ p6002)
    : p5078 ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5078) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6002) := (Or.elim h74339 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13003 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96310 (p2532 p3146 p5996 : Prop)
    (h74331 : (¬ p3146) ∨ (¬ p5996))
    (h12963 : p2532 ∨ p5996)
    : p2532 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2532) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5996) := (Or.elim h74331 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12963 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96311 (p2533 p3146 p5996 : Prop)
    (h74331 : (¬ p3146) ∨ (¬ p5996))
    (h12964 : p2533 ∨ p5996)
    : p2533 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2533) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5996) := (Or.elim h74331 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12964 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96313 (p3146 p5059 p5996 : Prop)
    (h74331 : (¬ p3146) ∨ (¬ p5996))
    (h12967 : p5059 ∨ p5996)
    : p5059 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5059) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5996) := (Or.elim h74331 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12967 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96314 (p3136 p5051 p5993 : Prop)
    (h74327 : (¬ p3136) ∨ (¬ p5993))
    (h12946 : p5051 ∨ p5993)
    : p5051 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5051) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5993) := (Or.elim h74327 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12946 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96315 (p3136 p4313 p5993 : Prop)
    (h74327 : (¬ p3136) ∨ (¬ p5993))
    (h12947 : p4313 ∨ p5993)
    : p4313 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4313) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5993) := (Or.elim h74327 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12947 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96317 (p3136 p5053 p5993 : Prop)
    (h74327 : (¬ p3136) ∨ (¬ p5993))
    (h12950 : p5053 ∨ p5993)
    : p5053 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5053) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5993) := (Or.elim h74327 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12950 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96318 (p3125 p5045 p5990 : Prop)
    (h74323 : (¬ p3125) ∨ (¬ p5990))
    (h12928 : p5045 ∨ p5990)
    : p5045 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5045) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5990) := (Or.elim h74323 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12928 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96319 (p3125 p4334 p5990 : Prop)
    (h74323 : (¬ p3125) ∨ (¬ p5990))
    (h12929 : p4334 ∨ p5990)
    : p4334 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4334) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5990) := (Or.elim h74323 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12929 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96321 (p3125 p4368 p5990 : Prop)
    (h74323 : (¬ p3125) ∨ (¬ p5990))
    (h12932 : p4368 ∨ p5990)
    : p4368 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4368) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5990) := (Or.elim h74323 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12932 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96322 (p3115 p4040 p5986 : Prop)
    (h74317 : p3115 ∨ (¬ p5986))
    (h12905 : p4040 ∨ p5986)
    : p4040 ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4040) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5986) := (Or.elim h74317 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12905 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96323 (p3115 p4314 p5986 : Prop)
    (h74317 : p3115 ∨ (¬ p5986))
    (h12907 : p4314 ∨ p5986)
    : p4314 ∨ p3115 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4314) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5986) := (Or.elim h74317 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12907 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96326 (p3105 p5026 p5983 : Prop)
    (h74313 : p3105 ∨ (¬ p5983))
    (h12887 : p5026 ∨ p5983)
    : p5026 ∨ p3105 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5026) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5983) := (Or.elim h74313 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12887 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96327 (p3105 p5025 p5983 : Prop)
    (h74313 : p3105 ∨ (¬ p5983))
    (h12889 : p5025 ∨ p5983)
    : p5025 ∨ p3105 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5025) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3105) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5983) := (Or.elim h74313 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12889 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96330 (p3073 p4352 p5975 : Prop)
    (h74303 : (¬ p3073) ∨ (¬ p5975))
    (h12840 : p4352 ∨ p5975)
    : p4352 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4352) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5975) := (Or.elim h74303 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12840 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96331 (p3073 p4351 p5975 : Prop)
    (h74303 : (¬ p3073) ∨ (¬ p5975))
    (h12841 : p4351 ∨ p5975)
    : p4351 ∨ (¬ p3073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4351) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5975) := (Or.elim h74303 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12841 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96334 (p3051 p4985 p5968 : Prop)
    (h74297 : p3051 ∨ (¬ p5968))
    (h12800 : p4985 ∨ p5968)
    : p4985 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4985) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5968) := (Or.elim h74297 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12800 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96335 (p3051 p4984 p5968 : Prop)
    (h74297 : p3051 ∨ (¬ p5968))
    (h12801 : p4984 ∨ p5968)
    : p4984 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4984) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5968) := (Or.elim h74297 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12801 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96336 (p3051 p4986 p5968 : Prop)
    (h74297 : p3051 ∨ (¬ p5968))
    (h12802 : p4986 ∨ p5968)
    : p4986 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4986) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5968) := (Or.elim h74297 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12802 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96337 (p3051 p3691 p5968 : Prop)
    (h74297 : p3051 ∨ (¬ p5968))
    (h12804 : p3691 ∨ p5968)
    : p3691 ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3691) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3051) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5968) := (Or.elim h74297 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12804 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96338 (p2992 p4959 p5960 : Prop)
    (h74287 : (¬ p2992) ∨ (¬ p5960))
    (h12744 : p4959 ∨ p5960)
    : p4959 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4959) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5960) := (Or.elim h74287 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12744 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96339 (p2992 p4282 p5960 : Prop)
    (h74287 : (¬ p2992) ∨ (¬ p5960))
    (h12745 : p4282 ∨ p5960)
    : p4282 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4282) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5960) := (Or.elim h74287 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12745 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96340 (p2992 p4365 p5960 : Prop)
    (h74287 : (¬ p2992) ∨ (¬ p5960))
    (h12746 : p4365 ∨ p5960)
    : p4365 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4365) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5960) := (Or.elim h74287 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12746 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96342 (p2982 p4947 p5956 : Prop)
    (h74281 : p2982 ∨ (¬ p5956))
    (h12719 : p4947 ∨ p5956)
    : p4947 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4947) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5956) := (Or.elim h74281 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12719 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96343 (p2982 p3237 p5956 : Prop)
    (h74281 : p2982 ∨ (¬ p5956))
    (h12721 : p3237 ∨ p5956)
    : p3237 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3237) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5956) := (Or.elim h74281 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12721 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96345 (p2982 p4950 p5956 : Prop)
    (h74281 : p2982 ∨ (¬ p5956))
    (h12723 : p4950 ∨ p5956)
    : p4950 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4950) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5956) := (Or.elim h74281 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12723 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96346 (p2972 p4388 p5953 : Prop)
    (h74277 : p2972 ∨ (¬ p5953))
    (h12701 : p4388 ∨ p5953)
    : p4388 ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4388) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5953) := (Or.elim h74277 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12701 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96347 (p2972 p4938 p5953 : Prop)
    (h74277 : p2972 ∨ (¬ p5953))
    (h12703 : p4938 ∨ p5953)
    : p4938 ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4938) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2972) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5953) := (Or.elim h74277 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12703 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96350 (p2901 p3699 p5947 : Prop)
    (h74269 : p2901 ∨ (¬ p5947))
    (h12664 : p3699 ∨ p5947)
    : p3699 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3699) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5947) := (Or.elim h74269 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12664 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96351 (p2901 p4386 p5947 : Prop)
    (h74269 : p2901 ∨ (¬ p5947))
    (h12666 : p4386 ∨ p5947)
    : p4386 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4386) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5947) := (Or.elim h74269 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12666 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96352 (p2901 p4917 p5947 : Prop)
    (h74269 : p2901 ∨ (¬ p5947))
    (h12667 : p4917 ∨ p5947)
    : p4917 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4917) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5947) := (Or.elim h74269 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12667 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96354 (p2891 p4909 p5944 : Prop)
    (h74265 : p2891 ∨ (¬ p5944))
    (h12647 : p4909 ∨ p5944)
    : p4909 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4909) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5944) := (Or.elim h74265 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12647 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96355 (p2891 p3554 p5944 : Prop)
    (h74265 : p2891 ∨ (¬ p5944))
    (h12649 : p3554 ∨ p5944)
    : p3554 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3554) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5944) := (Or.elim h74265 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12649 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96357 (p2891 p4911 p5944 : Prop)
    (h74265 : p2891 ∨ (¬ p5944))
    (h12651 : p4911 ∨ p5944)
    : p4911 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5944) := (Or.elim h74265 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12651 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96358 (p2881 p4042 p5942 : Prop)
    (h74263 : (¬ p2881) ∨ (¬ p5942))
    (h12636 : p4042 ∨ p5942)
    : p4042 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4042) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5942) := (Or.elim h74263 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12636 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96359 (p2881 p3747 p5942 : Prop)
    (h74263 : (¬ p2881) ∨ (¬ p5942))
    (h12637 : p3747 ∨ p5942)
    : p3747 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3747) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5942) := (Or.elim h74263 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12637 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96360 (p2881 p4904 p5942 : Prop)
    (h74263 : (¬ p2881) ∨ (¬ p5942))
    (h12639 : p4904 ∨ p5942)
    : p4904 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4904) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5942) := (Or.elim h74263 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12639 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96362 (p2870 p4169 p5938 : Prop)
    (h74257 : p2870 ∨ (¬ p5938))
    (h12611 : p4169 ∨ p5938)
    : p4169 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4169) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5938) := (Or.elim h74257 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12611 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96363 (p2870 p4136 p5938 : Prop)
    (h74257 : p2870 ∨ (¬ p5938))
    (h12613 : p4136 ∨ p5938)
    : p4136 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4136) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5938) := (Or.elim h74257 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12613 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96365 (p2870 p4895 p5938 : Prop)
    (h74257 : p2870 ∨ (¬ p5938))
    (h12615 : p4895 ∨ p5938)
    : p4895 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4895) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5938) := (Or.elim h74257 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12615 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96366 (p2850 p3695 p5933 : Prop)
    (h74251 : (¬ p2850) ∨ (¬ p5933))
    (h12582 : p3695 ∨ p5933)
    : p3695 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3695) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5933) := (Or.elim h74251 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12582 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96367 (p2850 p3582 p5933 : Prop)
    (h74251 : (¬ p2850) ∨ (¬ p5933))
    (h12583 : p3582 ∨ p5933)
    : p3582 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3582) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5933) := (Or.elim h74251 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12583 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96372 (p2839 p3371 p5930 : Prop)
    (h74247 : (¬ p2839) ∨ (¬ p5930))
    (h12567 : p3371 ∨ p5930)
    : p3371 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3371) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5930) := (Or.elim h74247 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12567 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96373 (p2839 p4243 p5930 : Prop)
    (h74247 : (¬ p2839) ∨ (¬ p5930))
    (h12569 : p4243 ∨ p5930)
    : p4243 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4243) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5930) := (Or.elim h74247 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12569 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96374 (p2829 p3953 p5926 : Prop)
    (h74241 : p2829 ∨ (¬ p5926))
    (h12543 : p3953 ∨ p5926)
    : p3953 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3953) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5926) := (Or.elim h74241 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12543 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96376 (p2829 p3918 p5926 : Prop)
    (h74241 : p2829 ∨ (¬ p5926))
    (h12545 : p3918 ∨ p5926)
    : p3918 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3918) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5926) := (Or.elim h74241 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12545 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96378 (p2819 p4326 p5924 : Prop)
    (h74239 : (¬ p2819) ∨ (¬ p5924))
    (h12530 : p4326 ∨ p5924)
    : p4326 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4326) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5924) := (Or.elim h74239 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12530 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96379 (p2819 p4861 p5924 : Prop)
    (h74239 : (¬ p2819) ∨ (¬ p5924))
    (h12531 : p4861 ∨ p5924)
    : p4861 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4861) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5924) := (Or.elim h74239 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12531 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96381 (p2819 p4863 p5924 : Prop)
    (h74239 : (¬ p2819) ∨ (¬ p5924))
    (h12534 : p4863 ∨ p5924)
    : p4863 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4863) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5924) := (Or.elim h74239 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12534 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96382 (p2797 p4328 p5918 : Prop)
    (h74231 : (¬ p2797) ∨ (¬ p5918))
    (h12491 : p4328 ∨ p5918)
    : p4328 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4328) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5918) := (Or.elim h74231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12491 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96383 (p2797 p4426 p5918 : Prop)
    (h74231 : (¬ p2797) ∨ (¬ p5918))
    (h12492 : p4426 ∨ p5918)
    : p4426 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4426) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5918) := (Or.elim h74231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12492 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96384 (p2797 p4845 p5918 : Prop)
    (h74231 : (¬ p2797) ∨ (¬ p5918))
    (h12494 : p4845 ∨ p5918)
    : p4845 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4845) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5918) := (Or.elim h74231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12494 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96385 (p2797 p4846 p5918 : Prop)
    (h74231 : (¬ p2797) ∨ (¬ p5918))
    (h12495 : p4846 ∨ p5918)
    : p4846 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4846) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5918) := (Or.elim h74231 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12495 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96386 (p2761 p4824 p5914 : Prop)
    (h74225 : p2761 ∨ (¬ p5914))
    (h12465 : p4824 ∨ p5914)
    : p4824 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4824) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5914) := (Or.elim h74225 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12465 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96387 (p2761 p4823 p5914 : Prop)
    (h74225 : p2761 ∨ (¬ p5914))
    (h12467 : p4823 ∨ p5914)
    : p4823 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4823) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5914) := (Or.elim h74225 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12467 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96390 (p2707 p4424 p5905 : Prop)
    (h74213 : p2707 ∨ (¬ p5905))
    (h12412 : p4424 ∨ p5905)
    : p4424 ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4424) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5905) := (Or.elim h74213 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12412 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96391 (p2707 p4794 p5905 : Prop)
    (h74213 : p2707 ∨ (¬ p5905))
    (h12413 : p4794 ∨ p5905)
    : p4794 ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4794) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5905) := (Or.elim h74213 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12413 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96392 (p2707 p4400 p5905 : Prop)
    (h74213 : p2707 ∨ (¬ p5905))
    (h12414 : p4400 ∨ p5905)
    : p4400 ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4400) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5905) := (Or.elim h74213 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12414 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96394 (p2685 p4325 p5900 : Prop)
    (h74207 : (¬ p2685) ∨ (¬ p5900))
    (h12383 : p4325 ∨ p5900)
    : p4325 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4325) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5900) := (Or.elim h74207 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12383 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96395 (p2685 p4781 p5900 : Prop)
    (h74207 : (¬ p2685) ∨ (¬ p5900))
    (h12384 : p4781 ∨ p5900)
    : p4781 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4781) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5900) := (Or.elim h74207 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12384 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96396 (p2685 p4782 p5900 : Prop)
    (h74207 : (¬ p2685) ∨ (¬ p5900))
    (h12386 : p4782 ∨ p5900)
    : p4782 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4782) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5900) := (Or.elim h74207 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12386 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96397 (p2685 p4783 p5900 : Prop)
    (h74207 : (¬ p2685) ∨ (¬ p5900))
    (h12387 : p4783 ∨ p5900)
    : p4783 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4783) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5900) := (Or.elim h74207 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12387 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96398 (p2668 p4417 p5897 : Prop)
    (h74203 : (¬ p2668) ∨ (¬ p5897))
    (h12366 : p4417 ∨ p5897)
    : p4417 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4417) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5897) := (Or.elim h74203 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12366 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96399 (p2668 p4341 p5897 : Prop)
    (h74203 : (¬ p2668) ∨ (¬ p5897))
    (h12367 : p4341 ∨ p5897)
    : p4341 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4341) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5897) := (Or.elim h74203 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12367 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96400 (p2668 p4773 p5897 : Prop)
    (h74203 : (¬ p2668) ∨ (¬ p5897))
    (h12369 : p4773 ∨ p5897)
    : p4773 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4773) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5897) := (Or.elim h74203 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12369 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96401 (p2668 p4774 p5897 : Prop)
    (h74203 : (¬ p2668) ∨ (¬ p5897))
    (h12370 : p4774 ∨ p5897)
    : p4774 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4774) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5897) := (Or.elim h74203 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12370 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96402 (p2630 p3683 p5891 : Prop)
    (h74195 : (¬ p2630) ∨ (¬ p5891))
    (h12331 : p3683 ∨ p5891)
    : p3683 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3683) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5891) := (Or.elim h74195 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12331 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96403 (p2630 p3475 p5891 : Prop)
    (h74195 : (¬ p2630) ∨ (¬ p5891))
    (h12332 : p3475 ∨ p5891)
    : p3475 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3475) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5891) := (Or.elim h74195 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12332 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96406 (p2608 p2753 p5884 : Prop)
    (h74185 : p2608 ∨ (¬ p5884))
    (h12291 : p2753 ∨ p5884)
    : p2753 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2753) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5884) := (Or.elim h74185 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12291 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96408 (p2608 p3873 p5884 : Prop)
    (h74185 : p2608 ∨ (¬ p5884))
    (h12294 : p3873 ∨ p5884)
    : p3873 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3873) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5884) := (Or.elim h74185 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12294 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96409 (p2563 p3096 p5878 : Prop)
    (h74177 : p2563 ∨ (¬ p5878))
    (h12257 : p3096 ∨ p5878)
    : p3096 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3096) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5878) := (Or.elim h74177 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12257 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96410 (p2563 p2590 p5878 : Prop)
    (h74177 : p2563 ∨ (¬ p5878))
    (h12259 : p2590 ∨ p5878)
    : p2590 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2590) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5878) := (Or.elim h74177 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12259 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96413 (p2440 p4241 p5873 : Prop)
    (h74171 : p2440 ∨ (¬ p5873))
    (h12228 : p4241 ∨ p5873)
    : p4241 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5873) := (Or.elim h74171 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12228 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96414 (p2440 p3413 p5873 : Prop)
    (h74171 : p2440 ∨ (¬ p5873))
    (h12229 : p3413 ∨ p5873)
    : p3413 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3413) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5873) := (Or.elim h74171 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12229 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96415 (p2440 p4705 p5873 : Prop)
    (h74171 : p2440 ∨ (¬ p5873))
    (h12232 : p4705 ∨ p5873)
    : p4705 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4705) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5873) := (Or.elim h74171 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12232 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96416 (p2459 p4445 p5863 : Prop)
    (h74161 : p2459 ∨ (¬ p5863))
    (h12168 : p4445 ∨ p5863)
    : p4445 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4445) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5863) := (Or.elim h74161 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12168 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96417 (p2459 p3657 p5863 : Prop)
    (h74161 : p2459 ∨ (¬ p5863))
    (h12170 : p3657 ∨ p5863)
    : p3657 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3657) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5863) := (Or.elim h74161 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12170 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96419 (p2459 p3950 p5863 : Prop)
    (h74161 : p2459 ∨ (¬ p5863))
    (h12172 : p3950 ∨ p5863)
    : p3950 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3950) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5863) := (Or.elim h74161 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12172 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96420 (p2449 p4660 p5861 : Prop)
    (h74159 : (¬ p2449) ∨ (¬ p5861))
    (h12157 : p4660 ∨ p5861)
    : p4660 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4660) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5861) := (Or.elim h74159 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12157 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96421 (p2449 p4661 p5861 : Prop)
    (h74159 : (¬ p2449) ∨ (¬ p5861))
    (h12158 : p4661 ∨ p5861)
    : p4661 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4661) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5861) := (Or.elim h74159 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12158 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96423 (p2449 p4663 p5861 : Prop)
    (h74159 : (¬ p2449) ∨ (¬ p5861))
    (h12161 : p4663 ∨ p5861)
    : p4663 ∨ (¬ p2449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4663) := (fun h => hn (Or.inl h));
    let u1 : p2449 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5861) := (Or.elim h74159 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12161 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96424 (p2417 p4451 p5852 : Prop)
    (h74147 : (¬ p2417) ∨ (¬ p5852))
    (h12106 : p4451 ∨ p5852)
    : p4451 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4451) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5852) := (Or.elim h74147 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12106 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96425 (p2417 p3192 p5852 : Prop)
    (h74147 : (¬ p2417) ∨ (¬ p5852))
    (h12107 : p3192 ∨ p5852)
    : p3192 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3192) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5852) := (Or.elim h74147 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12107 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96427 (p2417 p4641 p5852 : Prop)
    (h74147 : (¬ p2417) ∨ (¬ p5852))
    (h12110 : p4641 ∨ p5852)
    : p4641 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4641) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5852) := (Or.elim h74147 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12110 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96428 (p2406 p4210 p5849 : Prop)
    (h74143 : (¬ p2406) ∨ (¬ p5849))
    (h12088 : p4210 ∨ p5849)
    : p4210 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4210) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5849) := (Or.elim h74143 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12088 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96429 (p2406 p3948 p5849 : Prop)
    (h74143 : (¬ p2406) ∨ (¬ p5849))
    (h12089 : p3948 ∨ p5849)
    : p3948 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3948) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5849) := (Or.elim h74143 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12089 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96432 (p2383 p4617 p5843 : Prop)
    (h74135 : (¬ p2383) ∨ (¬ p5843))
    (h12052 : p4617 ∨ p5843)
    : p4617 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4617) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5843) := (Or.elim h74135 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12052 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96434 (p2383 p4114 p5843 : Prop)
    (h74135 : (¬ p2383) ∨ (¬ p5843))
    (h12055 : p4114 ∨ p5843)
    : p4114 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4114) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5843) := (Or.elim h74135 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12055 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96435 (p2383 p4113 p5843 : Prop)
    (h74135 : (¬ p2383) ∨ (¬ p5843))
    (h12056 : p4113 ∨ p5843)
    : p4113 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4113) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5843) := (Or.elim h74135 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12056 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96436 (p2363 p4171 p5836 : Prop)
    (h74125 : p2363 ∨ (¬ p5836))
    (h12010 : p4171 ∨ p5836)
    : p4171 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4171) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5836) := (Or.elim h74125 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12010 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96437 (p2363 p3322 p5836 : Prop)
    (h74125 : p2363 ∨ (¬ p5836))
    (h12012 : p3322 ∨ p5836)
    : p3322 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3322) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5836) := (Or.elim h74125 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12012 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96440 (p2352 p4157 p5834 : Prop)
    (h74123 : (¬ p2352) ∨ (¬ p5834))
    (h11997 : p4157 ∨ p5834)
    : p4157 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4157) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5834) := (Or.elim h74123 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11997 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96441 (p2352 p2510 p5834 : Prop)
    (h74123 : (¬ p2352) ∨ (¬ p5834))
    (h11998 : p2510 ∨ p5834)
    : p2510 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2510) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5834) := (Or.elim h74123 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11998 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96442 (p2352 p4598 p5834 : Prop)
    (h74123 : (¬ p2352) ∨ (¬ p5834))
    (h12000 : p4598 ∨ p5834)
    : p4598 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4598) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5834) := (Or.elim h74123 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12000 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96445 (p2341 p4592 p5831 : Prop)
    (h74119 : (¬ p2341) ∨ (¬ p5831))
    (h11981 : p4592 ∨ p5831)
    : p4592 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4592) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5831) := (Or.elim h74119 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11981 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96446 (p2341 p4403 p5831 : Prop)
    (h74119 : (¬ p2341) ∨ (¬ p5831))
    (h11982 : p4403 ∨ p5831)
    : p4403 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4403) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5831) := (Or.elim h74119 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11982 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96447 (p2341 p4590 p5831 : Prop)
    (h74119 : (¬ p2341) ∨ (¬ p5831))
    (h11983 : p4590 ∨ p5831)
    : p4590 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4590) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5831) := (Or.elim h74119 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11983 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96448 (p2331 p2667 p5828 : Prop)
    (h74115 : (¬ p2331) ∨ (¬ p5828))
    (h11963 : p2667 ∨ p5828)
    : p2667 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2667) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5828) := (Or.elim h74115 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11963 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96449 (p2331 p3987 p5828 : Prop)
    (h74115 : (¬ p2331) ∨ (¬ p5828))
    (h11965 : p3987 ∨ p5828)
    : p3987 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3987) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5828) := (Or.elim h74115 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11965 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96450 (p2331 p4583 p5828 : Prop)
    (h74115 : (¬ p2331) ∨ (¬ p5828))
    (h11966 : p4583 ∨ p5828)
    : p4583 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4583) := (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5828) := (Or.elim h74115 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11966 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96452 (p2295 p3552 p5825 : Prop)
    (h74111 : (¬ p2295) ∨ (¬ p5825))
    (h11946 : p3552 ∨ p5825)
    : p3552 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3552) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5825) := (Or.elim h74111 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11946 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96453 (p2295 p4156 p5825 : Prop)
    (h74111 : (¬ p2295) ∨ (¬ p5825))
    (h11947 : p4156 ∨ p5825)
    : p4156 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4156) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5825) := (Or.elim h74111 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11947 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96454 (p2295 p4572 p5825 : Prop)
    (h74111 : (¬ p2295) ∨ (¬ p5825))
    (h11949 : p4572 ∨ p5825)
    : p4572 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4572) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5825) := (Or.elim h74111 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11949 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96456 (p2264 p4378 p5816 : Prop)
    (h74099 : (¬ p2264) ∨ (¬ p5816))
    (h11894 : p4378 ∨ p5816)
    : p4378 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4378) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5816) := (Or.elim h74099 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11894 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96457 (p2264 p4044 p5816 : Prop)
    (h74099 : (¬ p2264) ∨ (¬ p5816))
    (h11895 : p4044 ∨ p5816)
    : p4044 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4044) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5816) := (Or.elim h74099 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11895 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96459 (p2264 p4041 p5816 : Prop)
    (h74099 : (¬ p2264) ∨ (¬ p5816))
    (h11898 : p4041 ∨ p5816)
    : p4041 ∨ (¬ p2264) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4041) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5816) := (Or.elim h74099 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11898 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96460 (p2220 p3697 p5809 : Prop)
    (h74089 : p2220 ∨ (¬ p5809))
    (h11853 : p3697 ∨ p5809)
    : p3697 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3697) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5809) := (Or.elim h74089 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11853 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96461 (p2220 p3696 p5809 : Prop)
    (h74089 : p2220 ∨ (¬ p5809))
    (h11854 : p3696 ∨ p5809)
    : p3696 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3696) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5809) := (Or.elim h74089 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11854 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96462 (p2220 p4529 p5809 : Prop)
    (h74089 : p2220 ∨ (¬ p5809))
    (h11856 : p4529 ∨ p5809)
    : p4529 ∨ p2220 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4529) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2220) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5809) := (Or.elim h74089 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11856 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96464 (p2210 p3369 p5806 : Prop)
    (h74085 : p2210 ∨ (¬ p5806))
    (h11835 : p3369 ∨ p5806)
    : p3369 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3369) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5806) := (Or.elim h74085 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11835 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96465 (p2210 p3370 p5806 : Prop)
    (h74085 : p2210 ∨ (¬ p5806))
    (h11836 : p3370 ∨ p5806)
    : p3370 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3370) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5806) := (Or.elim h74085 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11836 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96466 (p2210 p4521 p5806 : Prop)
    (h74085 : p2210 ∨ (¬ p5806))
    (h11838 : p4521 ∨ p5806)
    : p4521 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4521) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5806) := (Or.elim h74085 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11838 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96468 (p2192 p4512 p5803 : Prop)
    (h74081 : p2192 ∨ (¬ p5803))
    (h11817 : p4512 ∨ p5803)
    : p4512 ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4512) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5803) := (Or.elim h74081 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11817 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96469 (p2192 p3957 p5803 : Prop)
    (h74081 : p2192 ∨ (¬ p5803))
    (h11818 : p3957 ∨ p5803)
    : p3957 ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3957) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5803) := (Or.elim h74081 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11818 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96471 (p2192 p4514 p5803 : Prop)
    (h74081 : p2192 ∨ (¬ p5803))
    (h11821 : p4514 ∨ p5803)
    : p4514 ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4514) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5803) := (Or.elim h74081 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11821 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96472 (p2177 p3550 p5798 : Prop)
    (h74075 : (¬ p2177) ∨ (¬ p5798))
    (h11789 : p3550 ∨ p5798)
    : p3550 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3550) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5798) := (Or.elim h74075 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11789 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96473 (p2177 p3325 p5798 : Prop)
    (h74075 : (¬ p2177) ∨ (¬ p5798))
    (h11790 : p3325 ∨ p5798)
    : p3325 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3325) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5798) := (Or.elim h74075 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11790 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96475 (p2177 p4503 p5798 : Prop)
    (h74075 : (¬ p2177) ∨ (¬ p5798))
    (h11793 : p4503 ∨ p5798)
    : p4503 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4503) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5798) := (Or.elim h74075 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11793 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96476 (p2166 p3906 p5794 : Prop)
    (h74069 : p2166 ∨ (¬ p5794))
    (h11766 : p3906 ∨ p5794)
    : p3906 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3906) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5794) := (Or.elim h74069 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11766 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96477 (p2166 p4492 p5794 : Prop)
    (h74069 : p2166 ∨ (¬ p5794))
    (h11768 : p4492 ∨ p5794)
    : p4492 ∨ p2166 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4492) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2166) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5794) := (Or.elim h74069 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11768 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96481 (p2156 p4198 p5791 : Prop)
    (h74065 : p2156 ∨ (¬ p5791))
    (h11752 : p4198 ∨ p5791)
    : p4198 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4198) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5791) := (Or.elim h74065 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11752 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96482 (p2156 p3743 p5791 : Prop)
    (h74065 : p2156 ∨ (¬ p5791))
    (h11753 : p3743 ∨ p5791)
    : p3743 ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3743) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2156) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5791) := (Or.elim h74065 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h11753 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96483 (p2122 p4475 p5789 : Prop)
    (h74063 : (¬ p2122) ∨ (¬ p5789))
    (h11737 : p4475 ∨ p5789)
    : p4475 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4475) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5789) := (Or.elim h74063 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11737 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96484 (p2122 p3426 p5789 : Prop)
    (h74063 : (¬ p2122) ∨ (¬ p5789))
    (h11738 : p3426 ∨ p5789)
    : p3426 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3426) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5789) := (Or.elim h74063 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11738 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96485 (p2122 p4476 p5789 : Prop)
    (h74063 : (¬ p2122) ∨ (¬ p5789))
    (h11740 : p4476 ∨ p5789)
    : p4476 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4476) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5789) := (Or.elim h74063 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11740 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96486 (p2122 p4477 p5789 : Prop)
    (h74063 : (¬ p2122) ∨ (¬ p5789))
    (h11741 : p4477 ∨ p5789)
    : p4477 ∨ (¬ p2122) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4477) := (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5789) := (Or.elim h74063 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11741 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96487 (p2088 p4461 p5786 : Prop)
    (h74059 : (¬ p2088) ∨ (¬ p5786))
    (h11720 : p4461 ∨ p5786)
    : p4461 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4461) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5786) := (Or.elim h74059 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11720 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96490 (p2088 p4460 p5786 : Prop)
    (h74059 : (¬ p2088) ∨ (¬ p5786))
    (h11723 : p4460 ∨ p5786)
    : p4460 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4460) := (fun h => hn (Or.inl h));
    let u1 : p2088 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5786) := (Or.elim h74059 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11723 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96509 (p2098 p2104 p2598 p4149 p4286 p5369 p5616 p5682 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73204 : p2104 ∨ p2098)
    (h50430 : (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4286) ∨ (¬ p5369) ∨ (¬ p5616) ∨ (¬ p5682))
    : (¬ p5616) ∨ p4149 ∨ p2098 ∨ (¬ p5369) ∨ (¬ p2598) ∨ (¬ p5682) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5616 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4149) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2098) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5369 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5682 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50430 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step96513 (p2156 p2373 p3737 p3880 p4109 p4506 p5586 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h60583 : (¬ p2156) ∨ (¬ p3737) ∨ (¬ p3880) ∨ (¬ p4109) ∨ (¬ p4506) ∨ (¬ p5586))
    : (¬ p3737) ∨ (¬ p5586) ∨ p2373 ∨ (¬ p4506) ∨ (¬ p2156) ∨ (¬ p4109) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4109 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60583 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96514 (p2166 p2191 p2192 p3737 p4506 p5586 : Prop)
    (h73222 : p2191 ∨ p2166)
    (h64730 : (¬ p2191) ∨ (¬ p2192) ∨ (¬ p3737) ∨ (¬ p4506) ∨ (¬ p5586))
    : (¬ p3737) ∨ (¬ p5586) ∨ (¬ p4506) ∨ p2166 ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2166) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2191 := (Or.elim h73222 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64730 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96515 (p2088 p2363 p2785 p3857 p3914 p4197 p5586 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h56331 : (¬ p2363) ∨ (¬ p2785) ∨ (¬ p3857) ∨ (¬ p3914) ∨ (¬ p4197) ∨ (¬ p5586))
    : (¬ p3914) ∨ (¬ p5586) ∨ (¬ p4197) ∨ (¬ p2785) ∨ (¬ p2363) ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5586 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56331 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96517 (p2177 p2299 p3791 p5556 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h21839 : (¬ p2299) ∨ (¬ p3791) ∨ (¬ p5556))
    : (¬ p3791) ∨ (¬ p5556) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h21839 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96531 (p2177 p2493 p2499 p3801 p4260 p5507 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h62060 : (¬ p2177) ∨ (¬ p2499) ∨ (¬ p3801) ∨ (¬ p4260) ∨ (¬ p5507))
    : (¬ p3801) ∨ (¬ p4260) ∨ (¬ p2177) ∨ (¬ p5507) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3801 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5507 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62060 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96537 (p3707 p3767 p4321 p5487 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h39556 : (¬ p3767) ∨ (¬ p4321) ∨ (¬ p5487))
    : p3707 ∨ (¬ p5487) ∨ (¬ p3767) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p5487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h39556 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96543 (p3804 p3810 p3811 p3816 p5483 : Prop)
    (h73464 : p3810 ∨ p3804)
    (h73466 : p3816 ∨ p3811)
    (h9511 : (¬ p3810) ∨ (¬ p3816) ∨ (¬ p5483))
    : (¬ p5483) ∨ p3804 ∨ p3811 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3804) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3811) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3810 := (Or.elim h73464 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p3816 := (Or.elim h73466 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9511 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u0)))))))

theorem step96544 (p3794 p5479 p5482 p5483 : Prop)
    (h74042 : p5479 ∨ (¬ p3794))
    (h9512 : (¬ p5479) ∨ (¬ p5482) ∨ p5483)
    : (¬ p5482) ∨ p5483 ∨ (¬ p3794) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5482 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5483) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3794 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p5479 := (Or.elim h74042 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9512 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (u1 r1)))))))

theorem step96547 (p2449 p3246 p3947 p4067 p4228 p4275 p5477 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41538 : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4228) ∨ (¬ p4275) ∨ (¬ p5477))
    : (¬ p4228) ∨ (¬ p5477) ∨ (¬ p4275) ∨ (¬ p3246) ∨ (¬ p4067) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4228 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41538 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96548 (p2363 p3073 p3325 p4053 p4261 p4371 p5477 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h41676 : (¬ p2363) ∨ (¬ p3325) ∨ (¬ p4053) ∨ (¬ p4261) ∨ (¬ p4371) ∨ (¬ p5477))
    : (¬ p4053) ∨ p3073 ∨ (¬ p4371) ∨ (¬ p5477) ∨ (¬ p3325) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4053 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4371 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41676 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step96550 (p2264 p2298 p3527 p3548 p3914 p4024 p4105 p5477 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h58212 : (¬ p2264) ∨ (¬ p2298) ∨ (¬ p3548) ∨ (¬ p3914) ∨ (¬ p4024) ∨ (¬ p4105) ∨ (¬ p5477))
    : (¬ p3914) ∨ (¬ p5477) ∨ p3527 ∨ (¬ p2298) ∨ (¬ p2264) ∨ (¬ p4024) ∨ (¬ p4105) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3914 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5477 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2298 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4024 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58212 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u1)))))))))))))))

theorem step96554 (p2274 p3097 p3737 p4276 p5475 p5503 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h41769 : (¬ p3097) ∨ (¬ p3737) ∨ (¬ p4276) ∨ (¬ p5475) ∨ (¬ p5503))
    : (¬ p3737) ∨ (¬ p5475) ∨ (¬ p5503) ∨ (¬ p4276) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41769 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96555 (p2573 p2579 p3389 p4710 p5472 p5514 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h41904 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p5472) ∨ (¬ p5514))
    : (¬ p5514) ∨ p2573 ∨ (¬ p5472) ∨ (¬ p4710) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5514 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41904 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step96568 (p3276 p4425 p4952 p5402 p5403 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h16281 : (¬ p4425) ∨ (¬ p4952) ∨ (¬ p5402) ∨ (¬ p5403))
    : p3276 ∨ (¬ p5403) ∨ (¬ p4952) ∨ (¬ p5402) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p5403 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4952 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5402 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h16281 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step96574 (p3276 p3367 p3599 p4379 p4425 p5159 p5391 p5682 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h73578 : p4425 ∨ p3276)
    (h41967 : (¬ p3367) ∨ (¬ p4379) ∨ (¬ p4425) ∨ (¬ p5159) ∨ (¬ p5391) ∨ (¬ p5682))
    : p3599 ∨ p3276 ∨ (¬ p5159) ∨ (¬ p5682) ∨ (¬ p5391) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5159 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5682 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41967 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step96576 (p2255 p2641 p2667 p2891 p2946 p3246 p3412 p3461 p3773 p4154 p4625 p5378 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h48533 : (¬ p2255) ∨ (¬ p2667) ∨ (¬ p2891) ∨ (¬ p2946) ∨ (¬ p3246) ∨ (¬ p3412) ∨ (¬ p3461) ∨ (¬ p3773) ∨ (¬ p4154) ∨ (¬ p4625) ∨ (¬ p5378))
    : (¬ p3773) ∨ (¬ p3461) ∨ (¬ p2946) ∨ (¬ p5378) ∨ (¬ p2891) ∨ (¬ p2255) ∨ p2641 ∨ (¬ p3412) ∨ (¬ p3246) ∨ (¬ p2667) ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3773 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48533 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u10))) (fun r9 => (False.elim (r9 u3)))))))))))))))))))))))

theorem step96583 (p2753 p3599 p4233 p4379 p5352 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h32776 : (¬ p2753) ∨ (¬ p4233) ∨ (¬ p4379) ∨ (¬ p5352))
    : (¬ p2753) ∨ p3599 ∨ (¬ p5352) ∨ (¬ p4233) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h32776 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step96586 (p3670 p3707 p4321 p5332 p5387 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h74025 : (¬ p3670) ∨ (¬ p5387))
    (h26593 : (¬ p4321) ∨ (¬ p5332) ∨ p5387)
    : p3707 ∨ (¬ p5332) ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p5332 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p5387) := (Or.elim h74025 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h26593 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u4 r1)))))))

theorem step96592 (p2307 p2553 p2584 p2588 p3346 p5321 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h49495 : (¬ p2307) ∨ (¬ p2584) ∨ (¬ p2588) ∨ (¬ p3346) ∨ (¬ p5321))
    : (¬ p2307) ∨ (¬ p3346) ∨ p2553 ∨ (¬ p5321) ∨ (¬ p2584) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49495 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96597 (p2396 p2996 p3027 p3297 p3848 p5295 : Prop)
    (h73340 : p3027 ∨ p2996)
    (h72117 : (¬ p3848) ∨ (¬ p3297) ∨ (¬ p3027) ∨ (¬ p5295) ∨ (¬ p2396))
    : (¬ p3848) ∨ (¬ p3297) ∨ p2996 ∨ (¬ p2396) ∨ (¬ p5295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h72117 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96606 (p2341 p2696 p2797 p2881 p3246 p3323 p3365 p3570 p4037 p4195 p4625 p5257 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h73508 : p4037 ∨ p3323)
    (h73418 : p3570 ∨ p2881)
    (h53912 : (¬ p2341) ∨ (¬ p3246) ∨ (¬ p3365) ∨ (¬ p3570) ∨ (¬ p4037) ∨ (¬ p4195) ∨ (¬ p4625) ∨ (¬ p5257))
    : (¬ p2341) ∨ p2797 ∨ p2696 ∨ (¬ p3246) ∨ (¬ p5257) ∨ p3323 ∨ (¬ p4625) ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53912 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step96608 (p2753 p3425 p3471 p3599 p4379 p5234 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h73396 : p3471 ∨ p3425)
    (h20394 : (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4379) ∨ (¬ p5234))
    : p3599 ∨ (¬ p2753) ∨ p3425 ∨ (¬ p5234) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5234 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20394 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step96610 (p2707 p3246 p3588 p3599 p3690 p4898 p5233 : Prop)
    (h73430 : p3588 ∨ p2707)
    (h73446 : p3690 ∨ p3246)
    (h50506 : (¬ p3588) ∨ (¬ p3599) ∨ (¬ p3690) ∨ (¬ p4898) ∨ (¬ p5233))
    : (¬ p3599) ∨ (¬ p5233) ∨ p2707 ∨ p3246 ∨ (¬ p4898) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2707) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4898 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3588 := (Or.elim h73430 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50506 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96614 (p2717 p2753 p3425 p3471 p3599 p4379 p4666 p5229 : Prop)
    (h73572 : p4379 ∨ p3599)
    (h73396 : p3471 ∨ p3425)
    (h48941 : (¬ p2717) ∨ (¬ p2753) ∨ (¬ p3471) ∨ (¬ p4379) ∨ (¬ p4666) ∨ (¬ p5229))
    : (¬ p5229) ∨ (¬ p2753) ∨ (¬ p2717) ∨ p3599 ∨ (¬ p4666) ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5229 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3599) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4379 := (Or.elim h73572 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48941 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step96617 (p2761 p3670 p4381 p5229 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h20374 : (¬ p3670) ∨ (¬ p4381) ∨ (¬ p5229))
    : (¬ p3670) ∨ p2761 ∨ (¬ p5229) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5229 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20374 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96622 (p2630 p2737 p2743 p2810 p3599 p5177 p5458 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73298 : p2743 ∨ p2737)
    (h48435 : (¬ p2743) ∨ (¬ p2810) ∨ (¬ p3599) ∨ (¬ p5177) ∨ (¬ p5458))
    : (¬ p3599) ∨ (¬ p5458) ∨ p2630 ∨ (¬ p5177) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5458 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48435 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96625 (p2406 p3233 p3238 p3707 p4953 p5175 p5284 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h41660 : (¬ p3233) ∨ (¬ p3238) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p5175) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3707) ∨ (¬ p4953) ∨ (¬ p3233) ∨ p2406 ∨ (¬ p5175) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4953 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5175 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41660 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step96626 (p2663 p3286 p3292 p3355 p5171 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h20255 : (¬ p2663) ∨ (¬ p3292) ∨ (¬ p3355) ∨ (¬ p5171))
    : (¬ p5171) ∨ (¬ p3355) ∨ (¬ p2663) ∨ p3286 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5171 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3286) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h20255 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96627 (p2651 p2727 p3276 p3286 p3292 p4111 p4425 p5171 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73378 : p3292 ∨ p3286)
    (h73518 : p4111 ∨ p2727)
    (h43608 : (¬ p2651) ∨ (¬ p3292) ∨ (¬ p4111) ∨ (¬ p4425) ∨ (¬ p5171))
    : p3276 ∨ p3286 ∨ (¬ p2651) ∨ (¬ p5171) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3286) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43608 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96629 (p3276 p3506 p4425 p5171 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h20060 : (¬ p3506) ∨ (¬ p4425) ∨ (¬ p5171))
    : p3276 ∨ (¬ p3506) ∨ (¬ p5171) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20060 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96634 (p3193 p3276 p3422 p3584 p3670 p4425 p5165 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73426 : p3584 ∨ p3422)
    (h47021 : (¬ p3193) ∨ (¬ p3584) ∨ (¬ p3670) ∨ (¬ p4425) ∨ (¬ p5165))
    : p3276 ∨ (¬ p3670) ∨ (¬ p5165) ∨ (¬ p3193) ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5165 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47021 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96635 (p3276 p3346 p3422 p3584 p3660 p3670 p3905 p4425 p5165 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73426 : p3584 ∨ p3422)
    (h58816 : (¬ p3346) ∨ (¬ p3584) ∨ (¬ p3660) ∨ (¬ p3670) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p5165))
    : p3276 ∨ (¬ p3670) ∨ (¬ p3346) ∨ (¬ p3905) ∨ (¬ p3660) ∨ p3422 ∨ (¬ p5165) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5165 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h58816 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step96640 (p2156 p2241 p2247 p2727 p3125 p3461 p3892 p4111 p4521 p5133 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h48161 : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5133))
    : (¬ p3892) ∨ (¬ p5133) ∨ (¬ p2156) ∨ p2727 ∨ p2241 ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3892 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48161 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step96647 (p3146 p3461 p3692 p3969 p4191 p4330 p5121 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73448 : p3692 ∨ p3146)
    (h48255 : (¬ p3692) ∨ (¬ p3969) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p5121))
    : (¬ p3969) ∨ (¬ p5121) ∨ p3461 ∨ (¬ p4330) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3969 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5121 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48255 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96648 (p2427 p3571 p3670 p3707 p4235 p4321 p4885 p5031 p5357 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73536 : p4235 ∨ p2427)
    (h42522 : (¬ p3571) ∨ (¬ p3670) ∨ (¬ p4235) ∨ (¬ p4321) ∨ (¬ p4885) ∨ (¬ p5031) ∨ (¬ p5357))
    : p3707 ∨ (¬ p3670) ∨ (¬ p5031) ∨ (¬ p5357) ∨ (¬ p4885) ∨ p2427 ∨ (¬ p3571) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5357 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3571 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h42522 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step96651 (p2972 p3670 p4322 p4363 p4875 p5031 : Prop)
    (h73568 : p4363 ∨ p2972)
    (h54899 : (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4363) ∨ (¬ p4875) ∨ (¬ p5031))
    : (¬ p3670) ∨ (¬ p4322) ∨ (¬ p4875) ∨ (¬ p5031) ∨ p2972 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2972) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4363 := (Or.elim h73568 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54899 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96653 (p2839 p2982 p3583 p3599 p4885 p4948 p5030 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h73424 : p3583 ∨ p2839)
    (h42246 : (¬ p3583) ∨ (¬ p3599) ∨ (¬ p4885) ∨ (¬ p4948) ∨ (¬ p5030))
    : (¬ p3599) ∨ (¬ p5030) ∨ p2982 ∨ (¬ p4885) ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5030 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42246 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96664 (p2088 p2264 p2459 p3553 p4348 p4590 p4854 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73562 : p4348 ∨ p2459)
    (h64379 : (¬ p2088) ∨ (¬ p3553) ∨ (¬ p4348) ∨ (¬ p4590) ∨ (¬ p4854))
    : (¬ p4590) ∨ p2264 ∨ (¬ p4854) ∨ (¬ p2088) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64379 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96665 (p2870 p2982 p3698 p4129 p4382 p4830 p4948 : Prop)
    (h73846 : p4948 ∨ p2982)
    (h41429 : (¬ p2870) ∨ (¬ p3698) ∨ (¬ p4129) ∨ (¬ p4382) ∨ (¬ p4830) ∨ (¬ p4948))
    : (¬ p4129) ∨ (¬ p4830) ∨ (¬ p4382) ∨ p2982 ∨ (¬ p3698) ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4382 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41429 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step96667 (p3461 p3516 p3821 p4063 p4191 p4621 p4828 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73470 : p3821 ∨ p3516)
    (h49543 : (¬ p3821) ∨ (¬ p4063) ∨ (¬ p4191) ∨ (¬ p4621) ∨ (¬ p4828))
    : (¬ p4063) ∨ p3461 ∨ (¬ p4621) ∨ p3516 ∨ (¬ p4828) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4828 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49543 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96673 (p2598 p3367 p3399 p3585 p3589 p4366 p4793 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73428 : p3585 ∨ p3367)
    (h60037 : (¬ p2598) ∨ (¬ p3585) ∨ (¬ p3589) ∨ (¬ p4366) ∨ (¬ p4793))
    : (¬ p4793) ∨ p3399 ∨ (¬ p3589) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4793 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3589 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60037 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step96675 (p2253 p2651 p2727 p2741 p3399 p4111 p4366 p4793 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73570 : p4366 ∨ p3399)
    (h49575 : (¬ p2253) ∨ (¬ p2651) ∨ (¬ p2741) ∨ (¬ p4111) ∨ (¬ p4366) ∨ (¬ p4793))
    : p2727 ∨ (¬ p2253) ∨ (¬ p2651) ∨ (¬ p4793) ∨ (¬ p2741) ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3399) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49575 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step96676 (p3146 p3266 p3670 p3692 p4444 p4746 p5344 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h41210 : (¬ p3670) ∨ (¬ p3692) ∨ (¬ p4444) ∨ (¬ p4746) ∨ (¬ p5344))
    : (¬ p3670) ∨ p3266 ∨ (¬ p4746) ∨ (¬ p5344) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5344 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41210 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96679 (p2470 p2476 p3073 p3355 p4261 p4685 p4695 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73250 : p2476 ∨ p2470)
    (h48031 : (¬ p2476) ∨ (¬ p3355) ∨ (¬ p4261) ∨ (¬ p4685) ∨ (¬ p4695))
    : (¬ p3355) ∨ p3073 ∨ p2470 ∨ (¬ p4685) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3355 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48031 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96680 (p2156 p2274 p2396 p2630 p2696 p2753 p3097 p3343 p3645 p3646 p4107 p4638 p4877 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73436 : p3646 ∨ p2156)
    (h73352 : p3097 ∨ p2274)
    (h50794 : (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2753) ∨ (¬ p3097) ∨ (¬ p3343) ∨ (¬ p3645) ∨ (¬ p3646) ∨ (¬ p4107) ∨ (¬ p4638) ∨ (¬ p4877))
    : (¬ p4638) ∨ (¬ p3343) ∨ (¬ p2630) ∨ (¬ p2696) ∨ p2396 ∨ (¬ p4877) ∨ (¬ p2753) ∨ p2156 ∨ p2274 ∨ (¬ p3645) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4638 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3645 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h50794 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u5)))))))))))))))))))))

theorem step96681 (p2122 p2396 p2470 p2663 p2774 p2780 p3083 p3343 p3822 p4107 p4256 p4638 p4786 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73308 : p2780 ∨ p2774)
    (h73472 : p3822 ∨ p2122)
    (h73514 : p4107 ∨ p2396)
    (h52170 : (¬ p2470) ∨ (¬ p2663) ∨ (¬ p2780) ∨ (¬ p3343) ∨ (¬ p3822) ∨ (¬ p4107) ∨ (¬ p4256) ∨ (¬ p4638) ∨ (¬ p4786))
    : (¬ p2470) ∨ (¬ p3343) ∨ p3083 ∨ (¬ p2663) ∨ p2774 ∨ p2122 ∨ (¬ p4638) ∨ (¬ p4786) ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2774) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4638 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h52170 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step96682 (p2088 p2352 p3564 p3857 p3956 p4345 p4614 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73500 : p3956 ∨ p2352)
    (h41421 : (¬ p3564) ∨ (¬ p3857) ∨ (¬ p3956) ∨ (¬ p4345) ∨ (¬ p4614))
    : (¬ p3564) ∨ p2088 ∨ (¬ p4345) ∨ (¬ p4614) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4614 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41421 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96683 (p2122 p2230 p2307 p2589 p2655 p2819 p3146 p3256 p3822 p4118 p4134 p4346 p4580 p4607 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73284 : p2589 ∨ p2230)
    (h73472 : p3822 ∨ p2122)
    (h58480 : (¬ p2307) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2819) ∨ (¬ p3146) ∨ (¬ p3822) ∨ (¬ p4118) ∨ (¬ p4134) ∨ (¬ p4346) ∨ (¬ p4580) ∨ (¬ p4607))
    : (¬ p2819) ∨ p3256 ∨ (¬ p4607) ∨ (¬ p3146) ∨ (¬ p4580) ∨ (¬ p2655) ∨ p2230 ∨ p2122 ∨ (¬ p4134) ∨ (¬ p4346) ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4580 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2122) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3822 := (Or.elim h73472 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58480 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u4))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step96685 (p2264 p2331 p2341 p2963 p3553 p4104 p4572 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73410 : p3553 ∨ p2264)
    (h53033 : (¬ p2341) ∨ (¬ p2963) ∨ (¬ p3553) ∨ (¬ p4104) ∨ (¬ p4572))
    : (¬ p2341) ∨ p2331 ∨ (¬ p4104) ∨ p2264 ∨ (¬ p4572) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2331) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4572 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53033 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step96686 (p2088 p2532 p3115 p3156 p3497 p3857 p4529 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73400 : p3497 ∨ p3156)
    (h60831 : (¬ p2532) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3857) ∨ (¬ p4529))
    : (¬ p3115) ∨ p2088 ∨ (¬ p4529) ∨ (¬ p2532) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4529 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60831 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96687 (p2598 p2829 p3367 p3425 p3585 p4472 : Prop)
    (h73428 : p3585 ∨ p3367)
    (h55696 : (¬ p2598) ∨ (¬ p2829) ∨ (¬ p3425) ∨ (¬ p3585) ∨ (¬ p4472))
    : (¬ p2829) ∨ (¬ p3425) ∨ (¬ p4472) ∨ (¬ p2598) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55696 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96688 (p2761 p3146 p3657 p3767 p4381 p4456 p4905 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h53279 : (¬ p3146) ∨ (¬ p3657) ∨ (¬ p3767) ∨ (¬ p4381) ∨ (¬ p4456) ∨ (¬ p4905))
    : (¬ p3767) ∨ (¬ p4456) ∨ p2761 ∨ (¬ p3657) ∨ (¬ p4905) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2761) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53279 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step96689 (p3005 p3146 p3297 p3755 p4035 p4456 p5063 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h50550 : (¬ p3005) ∨ (¬ p3146) ∨ (¬ p3297) ∨ (¬ p4035) ∨ (¬ p4456) ∨ (¬ p5063))
    : p3755 ∨ (¬ p4456) ∨ (¬ p3297) ∨ (¬ p3005) ∨ (¬ p3146) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3297 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50550 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step96691 (p3146 p3322 p3461 p3767 p4134 p4191 p4456 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h63025 : (¬ p3146) ∨ (¬ p3322) ∨ (¬ p3767) ∨ (¬ p4134) ∨ (¬ p4191) ∨ (¬ p4456))
    : (¬ p3767) ∨ (¬ p3322) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4456) ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3767 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4456 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h63025 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step96693 (p2241 p2247 p3707 p3767 p3854 p4321 p4439 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h73226 : p2247 ∨ p2241)
    (h53841 : (¬ p2247) ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4321) ∨ (¬ p4439))
    : p3707 ∨ (¬ p3767) ∨ (¬ p3854) ∨ (¬ p4439) ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3767 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3854 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4439 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53841 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96696 (p2241 p2707 p2750 p2761 p3093 p3434 p3591 p4435 p5254 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h64558 : (¬ p2241) ∨ (¬ p2707) ∨ (¬ p2750) ∨ (¬ p2761) ∨ (¬ p3434) ∨ (¬ p3591) ∨ (¬ p4435) ∨ (¬ p5254))
    : (¬ p4435) ∨ (¬ p2241) ∨ (¬ p2750) ∨ p3093 ∨ (¬ p2707) ∨ (¬ p3434) ∨ (¬ p5254) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64558 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step96697 (p2819 p3093 p3591 p3914 p4358 p4435 : Prop)
    (h73564 : p4358 ∨ p2819)
    (h73432 : p3591 ∨ p3093)
    (h46726 : (¬ p3591) ∨ (¬ p3914) ∨ (¬ p4358) ∨ (¬ p4435))
    : (¬ p4435) ∨ (¬ p3914) ∨ p2819 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2819) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4358 := (Or.elim h73564 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46726 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step96699 (p2386 p2437 p3016 p3569 p3574 p4140 p4435 p5016 p5472 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h58001 : (¬ p2386) ∨ (¬ p2437) ∨ (¬ p3569) ∨ (¬ p3574) ∨ (¬ p4140) ∨ (¬ p4435) ∨ (¬ p5016) ∨ (¬ p5472))
    : (¬ p4435) ∨ (¬ p5472) ∨ (¬ p4140) ∨ (¬ p3569) ∨ (¬ p2437) ∨ (¬ p5016) ∨ p3016 ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58001 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step96700 (p2440 p3019 p3093 p3591 p4228 p4435 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h65003 : (¬ p2440) ∨ (¬ p3019) ∨ (¬ p3591) ∨ (¬ p4228) ∨ (¬ p4435))
    : (¬ p4435) ∨ (¬ p4228) ∨ p3093 ∨ (¬ p3019) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4228 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65003 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step96704 (p2341 p2608 p3093 p3146 p3266 p3543 p3591 p4132 p4435 p4793 p5254 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h63573 : (¬ p2341) ∨ (¬ p2608) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3543) ∨ (¬ p3591) ∨ (¬ p4132) ∨ (¬ p4435) ∨ (¬ p4793) ∨ (¬ p5254))
    : (¬ p4435) ∨ (¬ p4793) ∨ (¬ p2608) ∨ p3093 ∨ (¬ p5254) ∨ (¬ p3146) ∨ (¬ p4132) ∨ (¬ p2341) ∨ (¬ p3543) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4793 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3543 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63573 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u1))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step96705 (p2341 p2528 p2608 p3093 p3266 p3519 p3591 p4376 p4383 p4435 p5201 p5254 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h57349 : (¬ p2341) ∨ (¬ p2528) ∨ (¬ p2608) ∨ (¬ p3266) ∨ (¬ p3519) ∨ (¬ p3591) ∨ (¬ p4376) ∨ (¬ p4383) ∨ (¬ p4435) ∨ (¬ p5201) ∨ (¬ p5254))
    : (¬ p4435) ∨ (¬ p2341) ∨ p3093 ∨ (¬ p3519) ∨ (¬ p5254) ∨ (¬ p3266) ∨ (¬ p4383) ∨ (¬ p2608) ∨ (¬ p4376) ∨ (¬ p5201) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3093) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57349 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u4)))))))))))))))))))))))

theorem step96708 (p3201 p3876 p3914 p4210 p4375 p4435 p4512 p4644 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h63927 : (¬ p3876) ∨ (¬ p3914) ∨ (¬ p4210) ∨ (¬ p4375) ∨ (¬ p4435) ∨ (¬ p4512) ∨ (¬ p4644))
    : (¬ p4435) ∨ (¬ p3914) ∨ (¬ p4375) ∨ (¬ p4644) ∨ (¬ p4210) ∨ (¬ p4512) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4435 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3914 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h63927 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step96711 (p2274 p2957 p3097 p3136 p3370 p3737 p4315 p4435 p4512 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73352 : p3097 ∨ p2274)
    (h56756 : (¬ p2957) ∨ (¬ p3097) ∨ (¬ p3370) ∨ (¬ p3737) ∨ (¬ p4315) ∨ (¬ p4435) ∨ (¬ p4512))
    : (¬ p3370) ∨ (¬ p4435) ∨ p3136 ∨ (¬ p2957) ∨ (¬ p3737) ∨ (¬ p4512) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3370 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4512 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56756 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step96712 (p3073 p3146 p3692 p4119 p4140 p4317 p4435 p5472 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h41338 : (¬ p3073) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4140) ∨ (¬ p4317) ∨ (¬ p4435) ∨ (¬ p5472))
    : (¬ p4317) ∨ (¬ p4435) ∨ (¬ p5472) ∨ (¬ p4140) ∨ (¬ p4119) ∨ (¬ p3073) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4317 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5472 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4140 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h41338 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (False.elim (r5 u2)))))))))))))))

theorem step96713 (p2249 p2274 p2331 p2963 p2996 p3027 p3097 p3276 p3333 p3686 p3737 p3922 p4325 p4435 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73340 : p3027 ∨ p2996)
    (h73338 : p2963 ∨ p2331)
    (h52286 : (¬ p2249) ∨ (¬ p2963) ∨ (¬ p3027) ∨ (¬ p3097) ∨ (¬ p3276) ∨ (¬ p3333) ∨ (¬ p3686) ∨ (¬ p3737) ∨ (¬ p3922) ∨ p4325 ∨ (¬ p4435))
    : (¬ p3737) ∨ (¬ p4435) ∨ (¬ p2249) ∨ (¬ p3922) ∨ p2274 ∨ (¬ p3276) ∨ (¬ p3686) ∨ (¬ p3333) ∨ p2996 ∨ p4325 ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4435 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p4325) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    let u13 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h52286 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (u9 q9))) (fun r9 => (False.elim (r9 u1)))))))))))))))))))))))

theorem step96716 (p3680 p3707 p4321 p4387 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h20163 : (¬ p3680) ∨ (¬ p4321) ∨ (¬ p4387))
    : p3707 ∨ (¬ p3680) ∨ (¬ p4387) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20163 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96718 (p2210 p2982 p3555 p3830 p4387 p4632 p4948 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73846 : p4948 ∨ p2982)
    (h58766 : (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4387) ∨ (¬ p4632) ∨ (¬ p4948))
    : (¬ p4387) ∨ (¬ p3830) ∨ (¬ p4632) ∨ p2210 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h58766 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step96721 (p2210 p3115 p3555 p3830 p4208 p4387 p4960 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73412 : p3555 ∨ p2210)
    (h62858 : (¬ p3555) ∨ (¬ p3830) ∨ (¬ p4208) ∨ (¬ p4387) ∨ (¬ p4960))
    : (¬ p4387) ∨ (¬ p3830) ∨ (¬ p4960) ∨ p3115 ∨ p2210 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4387 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3115) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62858 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96723 (p2417 p2870 p3105 p4385 p4387 p4647 p5358 : Prop)
    (h73576 : p4385 ∨ p3105)
    (h50619 : (¬ p2417) ∨ (¬ p2870) ∨ (¬ p4385) ∨ (¬ p4387) ∨ (¬ p4647) ∨ (¬ p5358))
    : p3105 ∨ (¬ p5358) ∨ (¬ p4387) ∨ (¬ p2417) ∨ (¬ p2870) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p5358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4387 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50619 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step96724 (p2255 p2417 p2651 p2922 p2957 p2992 p3662 p3680 p3773 p3951 p4116 p4380 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h60190 : (¬ p2255) ∨ (¬ p2417) ∨ (¬ p2651) ∨ (¬ p2922) ∨ (¬ p2957) ∨ (¬ p3662) ∨ (¬ p3680) ∨ (¬ p3773) ∨ (¬ p3951) ∨ (¬ p4116) ∨ (¬ p4380))
    : (¬ p4116) ∨ p2992 ∨ (¬ p2651) ∨ (¬ p3680) ∨ (¬ p2922) ∨ (¬ p2255) ∨ (¬ p3951) ∨ (¬ p2417) ∨ (¬ p3773) ∨ (¬ p4380) ∨ (¬ p2957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4116 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3951 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3773 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4380 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60190 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u0))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step96730 (p2098 p2104 p2598 p4354 : Prop)
    (h73204 : p2104 ∨ p2098)
    (h6616 : (¬ p2104) ∨ (¬ p2598) ∨ (¬ p4354))
    : p2098 ∨ (¬ p4354) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2098) := (fun h => hn (Or.inl h));
    let u1 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2104 := (Or.elim h73204 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6616 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96732 (p3367 p3537 p4242 p4354 : Prop)
    (h73538 : p4242 ∨ p3537)
    (h33440 : (¬ p3367) ∨ (¬ p4242) ∨ (¬ p4354))
    : p3537 ∨ (¬ p4354) ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p4354 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h33440 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96739 (p2774 p2780 p3125 p3737 p3744 p4329 : Prop)
    (h73308 : p2780 ∨ p2774)
    (h73454 : p3744 ∨ p3125)
    (h46508 : (¬ p2780) ∨ (¬ p3737) ∨ (¬ p3744) ∨ (¬ p4329))
    : (¬ p3737) ∨ p2774 ∨ (¬ p4329) ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3737 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4329 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46508 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step96748 (p2417 p2870 p3105 p4244 p4277 p4278 p4323 p5299 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73540 : p4244 ∨ p2870)
    (h41754 : (¬ p3105) ∨ (¬ p4244) ∨ (¬ p4277) ∨ (¬ p4278) ∨ (¬ p4323) ∨ (¬ p5299))
    : (¬ p5299) ∨ p2417 ∨ (¬ p3105) ∨ (¬ p4323) ∨ (¬ p4277) ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5299 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41754 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step96760 (p3670 p3773 p4233 p5387 : Prop)
    (h74025 : (¬ p3670) ∨ (¬ p5387))
    (h32354 : (¬ p3773) ∨ (¬ p4233) ∨ p5387)
    : (¬ p3773) ∨ (¬ p4233) ∨ (¬ p3670) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3773 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4233 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p5387) := (Or.elim h74025 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h32354 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (u3 r1)))))))

theorem step96763 (p3276 p3346 p3670 p4231 p4375 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h72121 : (¬ p3670) ∨ (¬ p4425) ∨ (¬ p4231) ∨ (¬ p3346) ∨ (¬ p4375))
    : p3276 ∨ (¬ p3670) ∨ (¬ p4375) ∨ (¬ p4231) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3670 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4375 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4231 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h72121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96772 (p2156 p2957 p3136 p3646 p3755 p4039 p4315 p5046 : Prop)
    (h73550 : p4315 ∨ p3136)
    (h73436 : p3646 ∨ p2156)
    (h62079 : (¬ p2957) ∨ (¬ p3646) ∨ (¬ p3755) ∨ (¬ p4039) ∨ (¬ p4315) ∨ (¬ p5046))
    : (¬ p4039) ∨ (¬ p3755) ∨ p3136 ∨ (¬ p2957) ∨ (¬ p5046) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4039 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3755 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5046 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62079 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step96781 (p2156 p2241 p2247 p2727 p3125 p3461 p3892 p4111 p4521 p5127 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73226 : p2247 ∨ p2241)
    (h48162 : (¬ p2156) ∨ (¬ p2247) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p3892) ∨ (¬ p4111) ∨ (¬ p4521) ∨ (¬ p5127))
    : (¬ p3892) ∨ (¬ p5127) ∨ (¬ p4521) ∨ (¬ p2156) ∨ (¬ p3125) ∨ (¬ p3461) ∨ p2727 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3892 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5127 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u9 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48162 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step96782 (p2088 p3073 p3857 p3858 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h5706 : (¬ p3073) ∨ (¬ p3857) ∨ (¬ p3858))
    : (¬ p3073) ∨ p2088 ∨ (¬ p3858) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5706 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step96785 (p3852 p3853 p3856 : Prop)
    (h73477 : (¬ p3852) ∨ (¬ p3856))
    (h5698 : p3853 ∨ p3856)
    : p3853 ∨ (¬ p3852) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3853) := (fun h => hn (Or.inl h));
    let u1 : p3852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3856) := (Or.elim h73477 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5698 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96786 (p3852 p3854 p3856 : Prop)
    (h73477 : (¬ p3852) ∨ (¬ p3856))
    (h5699 : p3854 ∨ p3856)
    : p3854 ∨ (¬ p3852) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3854) := (fun h => hn (Or.inl h));
    let u1 : p3852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3856) := (Or.elim h73477 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5699 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96788 (p3833 p3852 p3856 : Prop)
    (h73477 : (¬ p3852) ∨ (¬ p3856))
    (h5701 : p3833 ∨ p3856)
    : p3833 ∨ (¬ p3852) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3833) := (fun h => hn (Or.inl h));
    let u1 : p3852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3856) := (Or.elim h73477 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5701 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96789 (p3842 p3852 p3856 : Prop)
    (h73477 : (¬ p3852) ∨ (¬ p3856))
    (h5702 : p3842 ∨ p3856)
    : p3842 ∨ (¬ p3852) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3842) := (fun h => hn (Or.inl h));
    let u1 : p3852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3856) := (Or.elim h73477 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5702 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96793 (p3506 p3707 p3853 p4321 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h6542 : (¬ p3506) ∨ (¬ p3853) ∨ (¬ p4321))
    : p3707 ∨ (¬ p3853) ∨ (¬ p3506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6542 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step96798 (p2249 p2573 p2656 p2727 p3266 p3286 p3292 p3564 p3707 p3853 p4321 p4330 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h73554 : p4321 ∨ p3707)
    (h62914 : (¬ p2249) ∨ (¬ p2573) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p3266) ∨ (¬ p3292) ∨ (¬ p3564) ∨ (¬ p3853) ∨ (¬ p4321) ∨ (¬ p4330))
    : p3286 ∨ p3707 ∨ (¬ p3564) ∨ (¬ p3853) ∨ (¬ p2573) ∨ (¬ p2249) ∨ (¬ p3266) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p4330) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3707) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h62914 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step96803 (p2608 p3136 p3755 p3830 p3834 p3847 p4315 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h73550 : p4315 ∨ p3136)
    (h59937 : (¬ p2608) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p4315))
    : (¬ p3755) ∨ p3830 ∨ (¬ p3847) ∨ (¬ p2608) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59937 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step96804 (p2255 p2957 p2992 p3051 p3246 p3286 p3461 p3556 p3662 p3690 p3707 p3847 p4191 p4621 : Prop)
    (h73440 : p3662 ∨ p2992)
    (h73414 : p3556 ∨ p3051)
    (h73530 : p4191 ∨ p3461)
    (h73446 : p3690 ∨ p3246)
    (h55721 : (¬ p2255) ∨ (¬ p2957) ∨ (¬ p3286) ∨ (¬ p3556) ∨ (¬ p3662) ∨ (¬ p3690) ∨ (¬ p3707) ∨ (¬ p3847) ∨ (¬ p4191) ∨ (¬ p4621))
    : (¬ p3707) ∨ p2992 ∨ (¬ p2957) ∨ (¬ p3286) ∨ p3051 ∨ p3461 ∨ (¬ p3847) ∨ (¬ p2255) ∨ p3246 ∨ (¬ p4621) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3461) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55721 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step96805 (p3707 p3847 p4321 p5284 : Prop)
    (h73553 : (¬ p3707) ∨ (¬ p4321))
    (h29669 : (¬ p3847) ∨ p4321 ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3847) ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4321) := (Or.elim h73553 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h29669 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step96806 (p3811 p3816 p5481 : Prop)
    (h73466 : p3816 ∨ p3811)
    (h9507 : p3811 ∨ (¬ p3816) ∨ p5481)
    : p3811 ∨ p5481 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3811) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5481) := (fun h => hn (Or.inr h));
    let u2 : p3816 := (Or.elim h73466 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h9507 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step96808 (p3804 p3810 p5480 : Prop)
    (h73464 : p3810 ∨ p3804)
    (h9503 : p3804 ∨ (¬ p3810) ∨ p5480)
    : p3804 ∨ p5480 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3804) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5480) := (fun h => hn (Or.inr h));
    let u2 : p3810 := (Or.elim h73464 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h9503 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u1 r1)))))))

theorem step96809 (p3804 p3807 p3810 : Prop)
    (h73463 : (¬ p3804) ∨ (¬ p3810))
    (h5610 : p3807 ∨ p3810)
    : p3807 ∨ (¬ p3804) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3807) := (fun h => hn (Or.inl h));
    let u1 : p3804 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3810) := (Or.elim h73463 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5610 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96819 (p3770 p3773 p3776 : Prop)
    (h73457 : (¬ p3770) ∨ (¬ p3776))
    (h5543 : p3773 ∨ p3776)
    : p3773 ∨ (¬ p3770) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3773) := (fun h => hn (Or.inl h));
    let u1 : p3770 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3776) := (Or.elim h73457 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h5543 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96826 (p2608 p3399 p3527 p3548 p3599 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73404 : p3548 ∨ p3527)
    (h47085 : (¬ p2608) ∨ (¬ p3548) ∨ (¬ p3599) ∨ (¬ p4366))
    : (¬ p3599) ∨ p3399 ∨ p3527 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47085 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step96831 (p2737 p2743 p3599 p5453 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h19937 : (¬ p2743) ∨ (¬ p3599) ∨ (¬ p5453))
    : (¬ p3599) ∨ (¬ p5453) ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h19937 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u1)))))))

theorem step96834 (p3146 p3537 p3599 p3692 p4242 p4746 p5343 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73538 : p4242 ∨ p3537)
    (h41212 : (¬ p3599) ∨ (¬ p3692) ∨ (¬ p4242) ∨ (¬ p4746) ∨ (¬ p5343))
    : (¬ p3599) ∨ p3146 ∨ p3537 ∨ (¬ p5343) ∨ (¬ p4746) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41212 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96835 (p2459 p3537 p3599 p4242 p4348 p4807 p5343 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73538 : p4242 ∨ p3537)
    (h42181 : (¬ p3599) ∨ (¬ p4242) ∨ (¬ p4348) ∨ (¬ p4807) ∨ (¬ p5343))
    : (¬ p3599) ∨ (¬ p5343) ∨ p2459 ∨ p3537 ∨ (¬ p4807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3537) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4242 := (Or.elim h73538 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42181 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step96837 (p3146 p3166 p3286 p3292 p3438 p3853 p5063 : Prop)
    (h73378 : p3292 ∨ p3286)
    (h53495 : (¬ p3146) ∨ (¬ p3166) ∨ (¬ p3292) ∨ (¬ p3438) ∨ (¬ p3853) ∨ (¬ p5063))
    : p3286 ∨ (¬ p3853) ∨ (¬ p3438) ∨ (¬ p5063) ∨ (¬ p3146) ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3286) := (fun h => hn (Or.inl h));
    let u1 : p3853 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3292 := (Or.elim h73378 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53495 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step96838 (p3266 p3438 p3707 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h20151 : (¬ p3438) ∨ (¬ p3707) ∨ (¬ p4444))
    : (¬ p3438) ∨ p3266 ∨ (¬ p3707) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3438 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20151 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step96840 (p2383 p2528 p3438 p3654 p3946 p4384 p5152 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h57697 : (¬ p2383) ∨ (¬ p2528) ∨ (¬ p3438) ∨ (¬ p3946) ∨ (¬ p4384) ∨ (¬ p5152))
    : (¬ p5152) ∨ p3654 ∨ (¬ p4384) ∨ (¬ p2383) ∨ (¬ p3438) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5152 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57697 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step96842 (p3286 p3297 p3301 : Prop)
    (h73383 : (¬ p3286) ∨ (¬ p3301))
    (h4721 : p3297 ∨ p3301)
    : p3297 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3297) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3301) := (Or.elim h73383 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4721 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96843 (p3286 p3298 p3301 : Prop)
    (h73383 : (¬ p3286) ∨ (¬ p3301))
    (h4722 : p3298 ∨ p3301)
    : p3298 ∨ (¬ p3286) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3298) := (fun h => hn (Or.inl h));
    let u1 : p3286 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3301) := (Or.elim h73383 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4722 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96852 (p3193 p3232 p3236 : Prop)
    (h73371 : p3193 ∨ (¬ p3236))
    (h4592 : p3232 ∨ p3236)
    : p3232 ∨ p3193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3232) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3236) := (Or.elim h73371 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4592 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96853 (p3193 p3233 p3236 : Prop)
    (h73371 : p3193 ∨ (¬ p3236))
    (h4593 : p3233 ∨ p3236)
    : p3233 ∨ p3193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3233) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3193) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3236) := (Or.elim h73371 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4593 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96857 (p2241 p2247 p3016 p3232 p3343 p3359 p3830 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73388 : p3359 ∨ p3343)
    (h45113 : (¬ p2247) ∨ (¬ p3016) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830))
    : (¬ p3830) ∨ (¬ p3232) ∨ p2241 ∨ (¬ p3016) ∨ p3343 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45113 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step96858 (p2440 p2542 p3232 p3343 p3359 p3399 p3830 p4366 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73388 : p3359 ∨ p3343)
    (h73270 : p2542 ∨ p2440)
    (h47287 : (¬ p2542) ∨ (¬ p3232) ∨ (¬ p3359) ∨ (¬ p3830) ∨ (¬ p4366))
    : p3399 ∨ (¬ p3830) ∨ p3343 ∨ p2440 ∨ (¬ p3232) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47287 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step96864 (p2396 p2761 p3232 p3707 p4276 p4321 p4635 : Prop)
    (h73554 : p4321 ∨ p3707)
    (h48337 : (¬ p2396) ∨ (¬ p2761) ∨ (¬ p3232) ∨ (¬ p4276) ∨ (¬ p4321) ∨ (¬ p4635))
    : p3707 ∨ (¬ p3232) ∨ (¬ p4635) ∨ (¬ p2761) ∨ (¬ p4276) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3707) := (fun h => hn (Or.inl h));
    let u1 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4321 := (Or.elim h73554 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48337 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step96866 (p3232 p3379 p3452 p3830 p5160 p5217 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h51544 : (¬ p3232) ∨ (¬ p3452) ∨ (¬ p3830) ∨ (¬ p5160) ∨ (¬ p5217))
    : (¬ p3830) ∨ p3379 ∨ (¬ p5217) ∨ (¬ p3232) ∨ (¬ p5160) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3232 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5160 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51544 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step96868 (p3193 p3229 p3379 p3452 p3830 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h65277 : (¬ p3193) ∨ (¬ p3229) ∨ (¬ p3452) ∨ (¬ p3830))
    : (¬ p3229) ∨ (¬ p3193) ∨ p3379 ∨ (¬ p3830) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3229 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65277 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step96873 (p3166 p3178 p3181 : Prop)
    (h73361 : (¬ p3166) ∨ (¬ p3181))
    (h4480 : p3178 ∨ p3181)
    : p3178 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3178) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3181) := (Or.elim h73361 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4480 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96874 (p3166 p3180 p3181 : Prop)
    (h73361 : (¬ p3166) ∨ (¬ p3181))
    (h4481 : p3180 ∨ p3181)
    : p3180 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3180) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3181) := (Or.elim h73361 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4481 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96876 (p3166 p3177 p3181 : Prop)
    (h73361 : (¬ p3166) ∨ (¬ p3181))
    (h4483 : p3177 ∨ p3181)
    : p3177 ∨ (¬ p3166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3177) := (fun h => hn (Or.inl h));
    let u1 : p3166 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3181) := (Or.elim h73361 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4483 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96881 (p2996 p3037 p3041 : Prop)
    (h73347 : p2996 ∨ (¬ p3041))
    (h4203 : p3037 ∨ p3041)
    : p3037 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3037) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3041) := (Or.elim h73347 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4203 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96882 (p2996 p3038 p3041 : Prop)
    (h73347 : p2996 ∨ (¬ p3041))
    (h4204 : p3038 ∨ p3041)
    : p3038 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3038) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3041) := (Or.elim h73347 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4204 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96883 (p2996 p3040 p3041 : Prop)
    (h73347 : p2996 ∨ (¬ p3041))
    (h4205 : p3040 ∨ p3041)
    : p3040 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3040) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3041) := (Or.elim h73347 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4205 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96884 (p2996 p3039 p3041 : Prop)
    (h73347 : p2996 ∨ (¬ p3041))
    (h4207 : p3039 ∨ p3041)
    : p3039 ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3039) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2996) := (fun h => hn (Or.inr h));
    let u2 : (¬ p3041) := (Or.elim h73347 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h4207 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96889 (p2807 p3034 p3166 p3414 p3527 p3548 p4378 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73392 : p3414 ∨ p2807)
    (h40989 : (¬ p3034) ∨ (¬ p3166) ∨ (¬ p3414) ∨ (¬ p3548) ∨ (¬ p4378))
    : (¬ p3166) ∨ (¬ p3034) ∨ p3527 ∨ (¬ p4378) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3527) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4378 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40989 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step96892 (p2946 p2959 p2961 : Prop)
    (h73335 : (¬ p2946) ∨ (¬ p2961))
    (h4047 : p2959 ∨ p2961)
    : p2959 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2959) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2961) := (Or.elim h73335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4047 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96894 (p2946 p2957 p2961 : Prop)
    (h73335 : (¬ p2946) ∨ (¬ p2961))
    (h4049 : p2957 ∨ p2961)
    : p2957 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2957) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2961) := (Or.elim h73335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4049 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96895 (p2946 p2958 p2961 : Prop)
    (h73335 : (¬ p2946) ∨ (¬ p2961))
    (h4050 : p2958 ∨ p2961)
    : p2958 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2958) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2961) := (Or.elim h73335 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4050 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96899 (p2922 p2934 p2937 : Prop)
    (h73325 : (¬ p2922) ∨ (¬ p2937))
    (h3997 : p2934 ∨ p2937)
    : p2934 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2934) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2937) := (Or.elim h73325 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3997 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96901 (p2922 p2936 p2937 : Prop)
    (h73325 : (¬ p2922) ∨ (¬ p2937))
    (h3999 : p2936 ∨ p2937)
    : p2936 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2936) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2937) := (Or.elim h73325 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3999 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96902 (p2922 p2933 p2937 : Prop)
    (h73325 : (¬ p2922) ∨ (¬ p2937))
    (h4000 : p2933 ∨ p2937)
    : p2933 ∨ (¬ p2922) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2933) := (fun h => hn (Or.inl h));
    let u1 : p2922 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2937) := (Or.elim h73325 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h4000 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96908 (p2774 p2781 p2783 : Prop)
    (h73309 : p2774 ∨ (¬ p2783))
    (h3687 : p2781 ∨ p2783)
    : p2781 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2781) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2783) := (Or.elim h73309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3687 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96910 (p2774 p2778 p2783 : Prop)
    (h73309 : p2774 ∨ (¬ p2783))
    (h3690 : p2778 ∨ p2783)
    : p2778 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2778) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2783) := (Or.elim h73309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3690 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96911 (p2774 p2779 p2783 : Prop)
    (h73309 : p2774 ∨ (¬ p2783))
    (h3691 : p2779 ∨ p2783)
    : p2779 ∨ p2774 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2779) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2783) := (Or.elim h73309 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3691 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96916 (p2187 p2274 p2307 p2528 p2598 p2781 p3055 p3097 p3609 p4340 p4384 p5368 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73350 : p3055 ∨ p2598)
    (h73558 : p4340 ∨ p3609)
    (h48890 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2528) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3097) ∨ (¬ p4340) ∨ (¬ p4384) ∨ (¬ p5368))
    : (¬ p2307) ∨ (¬ p5368) ∨ p2274 ∨ (¬ p4384) ∨ (¬ p2781) ∨ (¬ p2187) ∨ (¬ p2528) ∨ p2598 ∨ p3609 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5368 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3609) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u11 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h48890 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step96917 (p2383 p2598 p2781 p2850 p2982 p3055 p3266 p3461 p3684 p3990 p4444 p4948 p5059 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73846 : p4948 ∨ p2982)
    (h73350 : p3055 ∨ p2598)
    (h73442 : p3684 ∨ p2850)
    (h41936 : (¬ p2383) ∨ (¬ p2781) ∨ (¬ p3055) ∨ (¬ p3461) ∨ (¬ p3684) ∨ (¬ p3990) ∨ (¬ p4444) ∨ (¬ p4948) ∨ (¬ p5059))
    : p3266 ∨ (¬ p2383) ∨ p2982 ∨ p2598 ∨ (¬ p5059) ∨ (¬ p3990) ∨ (¬ p2781) ∨ (¬ p3461) ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41936 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step96920 (p2737 p2744 p2746 : Prop)
    (h73299 : p2737 ∨ (¬ p2746))
    (h3612 : p2744 ∨ p2746)
    : p2744 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2744) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2746) := (Or.elim h73299 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3612 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96922 (p2737 p2742 p2746 : Prop)
    (h73299 : p2737 ∨ (¬ p2746))
    (h3614 : p2742 ∨ p2746)
    : p2742 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2742) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2746) := (Or.elim h73299 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3614 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96923 (p2737 p2741 p2746 : Prop)
    (h73299 : p2737 ∨ (¬ p2746))
    (h3616 : p2741 ∨ p2746)
    : p2741 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2741) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2737) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2746) := (Or.elim h73299 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h3616 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96927 (p2651 p2663 p2666 : Prop)
    (h73293 : (¬ p2651) ∨ (¬ p2666))
    (h3453 : p2663 ∨ p2666)
    : p2663 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2663) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2666) := (Or.elim h73293 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3453 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96928 (p2651 p2662 p2666 : Prop)
    (h73293 : (¬ p2651) ∨ (¬ p2666))
    (h3455 : p2662 ∨ p2666)
    : p2662 ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2662) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2666) := (Or.elim h73293 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3455 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96934 (p2573 p2584 p2587 : Prop)
    (h73279 : (¬ p2573) ∨ (¬ p2587))
    (h3297 : p2584 ∨ p2587)
    : p2584 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2584) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2587) := (Or.elim h73279 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3297 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96935 (p2386 p2573 p2587 : Prop)
    (h73279 : (¬ p2573) ∨ (¬ p2587))
    (h3299 : p2386 ∨ p2587)
    : p2386 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2386) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2587) := (Or.elim h73279 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3299 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96943 (p2493 p2505 p2508 : Prop)
    (h73265 : (¬ p2493) ∨ (¬ p2508))
    (h3145 : p2505 ∨ p2508)
    : p2505 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2505) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2508) := (Or.elim h73265 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3145 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96944 (p2493 p2504 p2508 : Prop)
    (h73265 : (¬ p2493) ∨ (¬ p2508))
    (h3146 : p2504 ∨ p2508)
    : p2504 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2504) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2508) := (Or.elim h73265 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3146 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96945 (p2493 p2506 p2508 : Prop)
    (h73265 : (¬ p2493) ∨ (¬ p2508))
    (h3148 : p2506 ∨ p2508)
    : p2506 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2506) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2508) := (Or.elim h73265 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3148 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96946 (p2493 p2507 p2508 : Prop)
    (h73265 : (¬ p2493) ∨ (¬ p2508))
    (h3149 : p2507 ∨ p2508)
    : p2507 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2507) := (fun h => hn (Or.inl h));
    let u1 : p2493 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2508) := (Or.elim h73265 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3149 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96954 (p2470 p2481 p2485 : Prop)
    (h73255 : (¬ p2470) ∨ (¬ p2485))
    (h3100 : p2481 ∨ p2485)
    : p2481 ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2481) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2485) := (Or.elim h73255 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3100 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96955 (p2470 p2482 p2485 : Prop)
    (h73255 : (¬ p2470) ∨ (¬ p2485))
    (h3101 : p2482 ∨ p2485)
    : p2482 ∨ (¬ p2470) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2482) := (fun h => hn (Or.inl h));
    let u1 : p2470 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2485) := (Or.elim h73255 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h3101 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96962 (p2088 p2437 p2482 p2528 p2534 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73268 : p2534 ∨ p2528)
    (h56441 : (¬ p2088) ∨ (¬ p2437) ∨ (¬ p2482) ∨ (¬ p2534) ∨ (¬ p3540))
    : (¬ p2437) ∨ (¬ p2482) ∨ p3389 ∨ p2528 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2482 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56441 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step96966 (p2307 p2318 p2322 : Prop)
    (h73243 : (¬ p2307) ∨ (¬ p2322))
    (h2774 : p2318 ∨ p2322)
    : p2318 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2318) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2322) := (Or.elim h73243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2774 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96969 (p2307 p2319 p2322 : Prop)
    (h73243 : (¬ p2307) ∨ (¬ p2322))
    (h2778 : p2319 ∨ p2322)
    : p2319 ∨ (¬ p2307) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2319) := (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2322) := (Or.elim h73243 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2778 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96975 (p2241 p2246 p2250 : Prop)
    (h73227 : p2241 ∨ (¬ p2250))
    (h2630 : p2246 ∨ p2250)
    : p2246 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2250) := (Or.elim h73227 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2630 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96976 (p2241 p2245 p2250 : Prop)
    (h73227 : p2241 ∨ (¬ p2250))
    (h2632 : p2245 ∨ p2250)
    : p2245 ∨ p2241 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2245) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr h));
    let u2 : (¬ p2250) := (Or.elim h73227 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h2632 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96981 (p2132 p2143 p2147 : Prop)
    (h73219 : (¬ p2132) ∨ (¬ p2147))
    (h2426 : p2143 ∨ p2147)
    : p2143 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2143) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2147) := (Or.elim h73219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2426 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96982 (p2132 p2144 p2147 : Prop)
    (h73219 : (¬ p2132) ∨ (¬ p2147))
    (h2427 : p2144 ∨ p2147)
    : p2144 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2144) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2147) := (Or.elim h73219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2427 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96983 (p2132 p2145 p2147 : Prop)
    (h73219 : (¬ p2132) ∨ (¬ p2147))
    (h2429 : p2145 ∨ p2147)
    : p2145 ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2145) := (fun h => hn (Or.inl h));
    let u1 : p2132 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2147) := (Or.elim h73219 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2429 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96988 (p2098 p2109 p2113 : Prop)
    (h73209 : (¬ p2098) ∨ (¬ p2113))
    (h2358 : p2109 ∨ p2113)
    : p2109 ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2109) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2113) := (Or.elim h73209 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2358 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96989 (p2098 p2110 p2113 : Prop)
    (h73209 : (¬ p2098) ∨ (¬ p2113))
    (h2359 : p2110 ∨ p2113)
    : p2110 ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2110) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2113) := (Or.elim h73209 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2359 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step96990 (p2098 p2112 p2113 : Prop)
    (h73209 : (¬ p2098) ∨ (¬ p2113))
    (h2360 : p2112 ∨ p2113)
    : p2112 ∨ (¬ p2098) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2112) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p2113) := (Or.elim h73209 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h2360 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step97000 (p2363 p2459 p4138 p4347 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h23467 : (¬ p4138) ∨ p4347 ∨ (¬ p4348))
    : p2459 ∨ (¬ p4138) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h23467 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step97002 (p2363 p3146 p3692 p4347 p4441 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73559 : (¬ p2363) ∨ (¬ p4347))
    (h27620 : (¬ p3692) ∨ p4347 ∨ (¬ p4441))
    : (¬ p4441) ∨ p3146 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4441 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p4347) := (Or.elim h73559 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h27620 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step97015 (p2437 p3083 p3742 p4186 p4256 : Prop)
    (h73541 : (¬ p3083) ∨ (¬ p4256))
    (h73452 : p3742 ∨ p2437)
    (h6402 : (¬ p3742) ∨ (¬ p4186) ∨ p4256)
    : (¬ p3083) ∨ p2437 ∨ (¬ p4186) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4256) := (Or.elim h73541 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6402 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step97017 (p2470 p2476 p2662 p3083 p4256 : Prop)
    (h73541 : (¬ p3083) ∨ (¬ p4256))
    (h73250 : p2476 ∨ p2470)
    (h27047 : (¬ p2476) ∨ (¬ p2662) ∨ p4256)
    : (¬ p3083) ∨ p2470 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p4256) := (Or.elim h73541 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h27047 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (u3 r1)))))))

theorem step97019 (p2717 p2881 p3659 p4344 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h19748 : (¬ p2881) ∨ (¬ p3659) ∨ (¬ p4344))
    : (¬ p4344) ∨ p2717 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4344 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19748 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step97022 (p2717 p2881 p3105 p3659 p4136 p5104 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h57799 : (¬ p2881) ∨ (¬ p3105) ∨ (¬ p3659) ∨ (¬ p4136) ∨ (¬ p5104))
    : p2717 ∨ (¬ p3105) ∨ (¬ p2881) ∨ (¬ p4136) ∨ (¬ p5104) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3105 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5104 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57799 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step97024 (p2241 p2459 p2717 p2992 p3115 p3425 p3659 p4348 p4450 p4736 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73562 : p4348 ∨ p2459)
    (h55712 : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3115) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4348) ∨ (¬ p4450) ∨ (¬ p4736))
    : p2717 ∨ (¬ p3115) ∨ p2459 ∨ (¬ p3425) ∨ (¬ p2992) ∨ (¬ p4450) ∨ (¬ p2241) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4450 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h55712 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step97026 (p2717 p2774 p2829 p3425 p3659 p3688 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73444 : p3688 ∨ p2829)
    (h43840 : (¬ p2774) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p3688))
    : (¬ p3425) ∨ p2717 ∨ p2829 ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2829) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3688 := (Or.elim h73444 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43840 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step97027 (p2177 p2373 p2406 p2717 p3379 p3425 p3659 p4119 p4556 p4736 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h49702 : (¬ p2177) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p4736))
    : p2717 ∨ (¬ p3425) ∨ (¬ p4119) ∨ (¬ p4556) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p4736) ∨ (¬ p2177) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49702 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step97028 (p2192 p2210 p2459 p2717 p3125 p3425 p3659 p4330 p4348 p4736 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73562 : p4348 ∨ p2459)
    (h64061 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p3125) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4736))
    : p2717 ∨ (¬ p3125) ∨ (¬ p2210) ∨ (¬ p2192) ∨ (¬ p4736) ∨ (¬ p3425) ∨ (¬ p4330) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64061 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step97030 (p2156 p2192 p2717 p2891 p2911 p3425 p3659 p4172 p4173 p4647 p4736 : Prop)
    (h73528 : p4173 ∨ p2192)
    (h73438 : p3659 ∨ p2717)
    (h49618 : (¬ p2156) ∨ (¬ p2891) ∨ (¬ p2911) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4172) ∨ (¬ p4173) ∨ (¬ p4647) ∨ (¬ p4736))
    : (¬ p2891) ∨ p2192 ∨ (¬ p2911) ∨ (¬ p4647) ∨ (¬ p2156) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p4736) ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49618 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step97036 (p2459 p2518 p2717 p3379 p3425 p3659 p4149 p4348 p4736 p5122 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73562 : p4348 ∨ p2459)
    (h54077 : (¬ p2518) ∨ (¬ p3379) ∨ (¬ p3425) ∨ (¬ p3659) ∨ (¬ p4149) ∨ (¬ p4348) ∨ (¬ p4736) ∨ (¬ p5122))
    : (¬ p4149) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p3379) ∨ (¬ p2518) ∨ (¬ p5122) ∨ p2459 ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2518 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h54077 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step97041 (p2437 p2717 p2911 p3659 p3686 p4750 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h49303 : (¬ p2437) ∨ (¬ p2911) ∨ (¬ p3659) ∨ (¬ p3686) ∨ (¬ p4750))
    : p2717 ∨ (¬ p2911) ∨ (¬ p2437) ∨ (¬ p3686) ∨ (¬ p4750) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3686 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49303 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step97043 (p2088 p2717 p3256 p3659 p3857 p4044 p4403 p4779 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73438 : p3659 ∨ p2717)
    (h41030 : (¬ p3256) ∨ (¬ p3659) ∨ (¬ p3857) ∨ (¬ p4044) ∨ (¬ p4403) ∨ (¬ p4779))
    : (¬ p4403) ∨ p2088 ∨ (¬ p3256) ∨ (¬ p4044) ∨ p2717 ∨ (¬ p4779) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4403 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4044 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4779 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41030 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step97045 (p2717 p2761 p3659 p3670 p4381 p4668 p5234 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73438 : p3659 ∨ p2717)
    (h50530 : (¬ p3659) ∨ (¬ p3670) ∨ (¬ p4381) ∨ (¬ p4668) ∨ (¬ p5234))
    : (¬ p3670) ∨ p2761 ∨ p2717 ∨ (¬ p5234) ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5234 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50530 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step97047 (p2331 p2717 p3425 p3461 p3506 p3659 p4191 p4200 p4330 p4421 p4786 p5558 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73438 : p3659 ∨ p2717)
    (h56978 : (¬ p2331) ∨ (¬ p3425) ∨ (¬ p3506) ∨ (¬ p3659) ∨ (¬ p4191) ∨ (¬ p4200) ∨ (¬ p4330) ∨ (¬ p4421) ∨ (¬ p4786) ∨ (¬ p5558))
    : (¬ p3506) ∨ p3461 ∨ (¬ p5558) ∨ p2717 ∨ (¬ p4200) ∨ (¬ p3425) ∨ (¬ p2331) ∨ (¬ p4330) ∨ (¬ p4786) ∨ (¬ p4421) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3506 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4200 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4421 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56978 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step97050 (p2331 p2717 p3323 p3425 p3461 p3659 p4786 p5123 p5558 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h42462 : (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3425) ∨ (¬ p3461) ∨ (¬ p3659) ∨ (¬ p4786) ∨ (¬ p5123) ∨ (¬ p5558))
    : (¬ p5558) ∨ (¬ p5123) ∨ (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3425) ∨ p2717 ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5558 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h42462 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step97051 (p2230 p2437 p2440 p2542 p2589 p2717 p3399 p3527 p3659 p3742 p5083 p5193 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h73284 : p2589 ∨ p2230)
    (h41551 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3742) ∨ (¬ p5083) ∨ (¬ p5193))
    : (¬ p3527) ∨ p2717 ∨ p2440 ∨ (¬ p5193) ∨ p2437 ∨ p2230 ∨ (¬ p5083) ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5083 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41551 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step97057 (p2717 p2839 p3527 p3583 p3659 p3687 p4897 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73424 : p3583 ∨ p2839)
    (h48453 : (¬ p3527) ∨ (¬ p3583) ∨ (¬ p3659) ∨ (¬ p3687) ∨ (¬ p4897))
    : (¬ p3687) ∨ (¬ p3527) ∨ (¬ p4897) ∨ p2717 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3687 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4897 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2839) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3583 := (Or.elim h73424 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48453 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step97058 (p2608 p2717 p3399 p3527 p3659 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73438 : p3659 ∨ p2717)
    (h45253 : (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3659) ∨ (¬ p3954))
    : (¬ p3527) ∨ p2608 ∨ p2717 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2717) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45253 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step97060 (p2264 p2630 p2717 p2807 p3553 p3659 p4117 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73409 : (¬ p2264) ∨ (¬ p3553))
    (h66986 : p3553 ∨ (¬ p3659) ∨ (¬ p2807) ∨ (¬ p2630) ∨ (¬ p4117))
    : p2717 ∨ (¬ p2264) ∨ (¬ p4117) ∨ (¬ p2630) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : (¬ p3553) := (Or.elim h73409 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h66986 (fun q0 => (False.elim (u6 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step97061 (p2717 p3366 p3379 p3425 p3452 p3659 p3707 p3830 p4042 p4376 p5123 p5568 : Prop)
    (h73438 : p3659 ∨ p2717)
    (h73394 : p3452 ∨ p3379)
    (h64946 : (¬ p3366) ∨ (¬ p3425) ∨ (¬ p3452) ∨ (¬ p3659) ∨ (¬ p3707) ∨ (¬ p3830) ∨ (¬ p4042) ∨ (¬ p4376) ∨ (¬ p5123) ∨ (¬ p5568))
    : (¬ p5568) ∨ p2717 ∨ (¬ p4042) ∨ (¬ p3425) ∨ (¬ p3366) ∨ (¬ p3830) ∨ (¬ p5123) ∨ (¬ p4376) ∨ (¬ p3707) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3425 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3830 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5123 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3707 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3659 := (Or.elim h73438 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64946 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u6))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

end ElevenRUP
