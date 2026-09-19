import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step78732 (p2284 p3146 p3256 p3661 p4118 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h69478 : (¬ p4118) ∨ (¬ p2284) ∨ (¬ p3661) ∨ (¬ p3146))
    : (¬ p3661) ∨ p3256 ∨ (¬ p2284) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3661 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h69478 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step78733 (p2619 p3146 p3256 p3661 p4118 p5053 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h41764 : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p5053))
    : p3256 ∨ (¬ p3661) ∨ (¬ p5053) ∨ (¬ p2619) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5053 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41764 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78734 (p2396 p2459 p2881 p3146 p4107 p4559 p4665 p4903 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73820 : p4903 ∨ (¬ p2881))
    (h73696 : p4665 ∨ p2459)
    (h65751 : (¬ p4665) ∨ (¬ p3146) ∨ (¬ p4903) ∨ (¬ p4107) ∨ (¬ p4559))
    : p2396 ∨ (¬ p2881) ∨ (¬ p4559) ∨ p2459 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4903 := (Or.elim h73820 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u7 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65751 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78738 (p3146 p3246 p3690 p3747 p4445 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h39274 : (¬ p3146) ∨ (¬ p3690) ∨ (¬ p3747) ∨ (¬ p4445))
    : (¬ p3747) ∨ (¬ p4445) ∨ p3246 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3747 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h39274 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step78739 (p2459 p2911 p3146 p3644 p3747 p4277 p4348 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h59137 : (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3747) ∨ (¬ p4277) ∨ (¬ p4348))
    : p2911 ∨ (¬ p3747) ∨ p2459 ∨ (¬ p3146) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59137 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78741 (p2177 p2299 p2459 p3146 p3747 p4348 p4559 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73562 : p4348 ∨ p2459)
    (h41325 : (¬ p2299) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p4348) ∨ (¬ p4559))
    : p2177 ∨ (¬ p3747) ∨ (¬ p3146) ∨ p2459 ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41325 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78742 (p2528 p2534 p3146 p3379 p3449 p3860 p4370 : Prop)
    (h73482 : p3860 ∨ p3449)
    (h73268 : p2534 ∨ p2528)
    (h54888 : (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3379) ∨ (¬ p3860) ∨ (¬ p4370))
    : p3449 ∨ p2528 ∨ (¬ p4370) ∨ (¬ p3146) ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3860 := (Or.elim h73482 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54888 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78744 (p2177 p2396 p3146 p4107 p4445 p4905 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h41698 : (¬ p2177) ∨ (¬ p3146) ∨ (¬ p4107) ∨ (¬ p4445) ∨ (¬ p4905))
    : p2396 ∨ (¬ p4905) ∨ (¬ p4445) ∨ (¬ p2177) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41698 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78747 (p2459 p2946 p3146 p3156 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h44634 : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4348))
    : (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3146) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44634 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78749 (p2166 p2255 p2307 p2313 p2396 p2641 p2667 p2946 p3146 p3412 p4107 p4154 p4669 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73514 : p4107 ∨ p2396)
    (h73238 : p2313 ∨ p2307)
    (h56041 : (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2313) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3412) ∨ (¬ p4107) ∨ (¬ p4154) ∨ (¬ p4669))
    : (¬ p3412) ∨ p2641 ∨ (¬ p2166) ∨ (¬ p2946) ∨ (¬ p3146) ∨ p2396 ∨ (¬ p4669) ∨ p2307 ∨ (¬ p2667) ∨ (¬ p2255) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3412 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h56041 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step78750 (p2166 p2210 p2254 p2417 p2437 p2651 p2657 p3146 p3742 p4278 p4669 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73288 : p2657 ∨ p2651)
    (h73452 : p3742 ∨ p2437)
    (h51955 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3742) ∨ (¬ p4278) ∨ (¬ p4669))
    : p2417 ∨ (¬ p3146) ∨ (¬ p2166) ∨ (¬ p4669) ∨ p2651 ∨ p2437 ∨ (¬ p2210) ∨ (¬ p2254) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h51955 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78754 (p2264 p2449 p3146 p3947 p4445 p4905 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41890 : (¬ p2264) ∨ (¬ p3146) ∨ (¬ p3947) ∨ (¬ p4445) ∨ (¬ p4905))
    : p2449 ∨ (¬ p2264) ∨ (¬ p3146) ∨ (¬ p4445) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41890 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78755 (p2284 p2459 p2901 p3146 p3747 p3952 p4348 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73562 : p4348 ∨ p2459)
    (h58062 : (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3747) ∨ (¬ p3952) ∨ (¬ p4348))
    : (¬ p2901) ∨ (¬ p3747) ∨ p2284 ∨ p2459 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3747 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58062 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78756 (p2284 p2563 p3146 p3156 p3952 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h47230 : (¬ p2563) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3952))
    : (¬ p3156) ∨ p2284 ∨ (¬ p3146) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47230 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78757 (p2427 p2957 p3051 p3146 p3156 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h57945 : (¬ p2427) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3556))
    : (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p2427) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2957 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h57945 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78758 (p2363 p2946 p3146 p3156 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h43214 : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4347))
    : (¬ p3146) ∨ p2363 ∨ (¬ p2946) ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43214 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78760 (p2295 p2307 p2470 p2476 p2528 p2534 p2668 p2781 p3146 p3568 p3905 p4134 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h58989 : (¬ p2307) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p2781) ∨ (¬ p3146) ∨ (¬ p3568) ∨ (¬ p3905) ∨ (¬ p4134))
    : (¬ p2307) ∨ (¬ p2668) ∨ (¬ p4134) ∨ p2295 ∨ p2528 ∨ (¬ p3146) ∨ p2470 ∨ (¬ p2781) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2307 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2781 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h58989 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u2)))))))))))))))))))

theorem step78761 (p2528 p2534 p2651 p2657 p3083 p3146 p4236 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73288 : p2657 ∨ p2651)
    (h45656 : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p4236) ∨ (¬ p4256))
    : p2528 ∨ (¬ p4236) ∨ (¬ p3146) ∨ p3083 ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45656 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78762 (p2190 p2528 p2534 p3146 p3922 p3923 p4157 p4564 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h57566 : (¬ p2190) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3922) ∨ (¬ p3923) ∨ (¬ p4157) ∨ (¬ p4564))
    : (¬ p4157) ∨ p2528 ∨ (¬ p3923) ∨ (¬ p3922) ∨ (¬ p2190) ∨ (¬ p3146) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4157 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57566 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step78763 (p2241 p2247 p2470 p2476 p2528 p2534 p2744 p3063 p3093 p3146 p3366 p3905 p4134 : Prop)
    (h73226 : p2247 ∨ p2241)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h52998 : (¬ p2247) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2744) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3366) ∨ (¬ p3905) ∨ (¬ p4134))
    : (¬ p3063) ∨ p2241 ∨ (¬ p3366) ∨ (¬ p2744) ∨ (¬ p4134) ∨ p2470 ∨ p2528 ∨ (¬ p3146) ∨ (¬ p3905) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52998 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step78767 (p2122 p2177 p2470 p2476 p2528 p2534 p2774 p3146 p4108 p4733 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h64084 : (¬ p2122) ∨ (¬ p2177) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3146) ∨ (¬ p4108) ∨ (¬ p4733) ∨ (¬ p4905))
    : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p4733) ∨ (¬ p3146) ∨ (¬ p2177) ∨ p2528 ∨ (¬ p4108) ∨ p2470 ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64084 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step78770 (p2220 p2528 p2534 p3146 p4539 p4607 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h50820 : (¬ p2220) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p4539) ∨ (¬ p4607))
    : (¬ p4607) ∨ (¬ p3146) ∨ p2528 ∨ (¬ p4539) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4607 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50820 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step78773 (p2441 p2528 p2534 p3146 p3156 p4186 p4705 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h58446 : (¬ p2441) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4186) ∨ (¬ p4705))
    : p2528 ∨ (¬ p3146) ∨ (¬ p4186) ∨ (¬ p4705) ∨ (¬ p3156) ∨ (¬ p2441) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4186 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58446 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step78774 (p2177 p2295 p2331 p2470 p2476 p2528 p2534 p3146 p3905 p4786 p4905 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h52115 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p4905))
    : (¬ p2295) ∨ p2528 ∨ p2470 ∨ (¬ p2177) ∨ (¬ p4905) ∨ (¬ p4786) ∨ (¬ p3146) ∨ (¬ p2331) ∨ (¬ p3905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52115 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u5))) (fun r7 => (False.elim (r7 u4)))))))))))))))))))

theorem step78775 (p2406 p2509 p2528 p2534 p3146 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h48987 : (¬ p2406) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3146))
    : (¬ p2509) ∨ p2528 ∨ (¬ p3146) ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h48987 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step78777 (p2352 p3146 p3564 p4134 p4137 p4171 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h41591 : (¬ p2352) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p4137) ∨ (¬ p4171))
    : p3564 ∨ (¬ p4171) ∨ (¬ p3146) ∨ (¬ p2352) ∨ (¬ p4134) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41591 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78779 (p2295 p2363 p2668 p3146 p3324 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h43295 : (¬ p2295) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2295) ∨ p2363 ∨ (¬ p3146) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43295 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78783 (p2190 p2363 p2668 p3146 p3324 p4347 p4564 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h55133 : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p3324) ∨ (¬ p4347) ∨ (¬ p4564))
    : p2363 ∨ (¬ p3146) ∨ (¬ p2190) ∨ p2668 ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55133 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78787 (p2230 p2363 p2373 p3146 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h42647 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3146) ∨ (¬ p2373) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42647 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78791 (p3146 p3266 p3461 p3657 p4191 p4623 p4905 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h41401 : (¬ p3146) ∨ (¬ p3266) ∨ (¬ p3657) ∨ (¬ p4191) ∨ (¬ p4623) ∨ (¬ p4905))
    : p3461 ∨ (¬ p3266) ∨ (¬ p4905) ∨ (¬ p3657) ∨ (¬ p3146) ∨ (¬ p4623) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3657 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41401 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78793 (p2255 p2383 p2387 p2641 p2667 p2946 p3146 p3156 p4154 p5118 p5580 : Prop)
    (h73526 : p4154 ∨ p2641)
    (h73246 : p2387 ∨ p2383)
    (h49676 : (¬ p2255) ∨ (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4154) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ p2641 ∨ (¬ p3156) ∨ p2383 ∨ (¬ p2667) ∨ (¬ p2255) ∨ (¬ p2946) ∨ (¬ p5118) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49676 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step78795 (p2241 p2470 p2476 p2528 p2534 p2641 p2668 p3146 p4134 p5193 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h50284 : (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3146) ∨ (¬ p4134) ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3146) ∨ p2470 ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p4134) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50284 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step78796 (p2373 p2427 p2459 p3146 p4235 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73536 : p4235 ∨ p2427)
    (h45390 : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p4235) ∨ (¬ p4348))
    : (¬ p2373) ∨ p2459 ∨ (¬ p3146) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45390 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78798 (p2373 p2427 p3146 p3266 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h60656 : (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3266) ∨ (¬ p4235))
    : (¬ p2373) ∨ p2427 ∨ (¬ p3146) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60656 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78800 (p2190 p2440 p2528 p2534 p2651 p2657 p3146 p4607 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73268 : p2534 ∨ p2528)
    (h61893 : (¬ p2190) ∨ (¬ p2440) ∨ (¬ p2534) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p4607))
    : (¬ p2190) ∨ p2651 ∨ (¬ p3146) ∨ (¬ p2440) ∨ (¬ p4607) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h61893 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step78801 (p2190 p2427 p2528 p2534 p3146 p4558 p4607 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h50585 : (¬ p2190) ∨ (¬ p2427) ∨ (¬ p2534) ∨ (¬ p3146) ∨ (¬ p4558) ∨ (¬ p4607))
    : (¬ p2190) ∨ (¬ p4607) ∨ p2528 ∨ (¬ p2427) ∨ (¬ p4558) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50585 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step78802 (p2248 p2417 p2922 p2928 p2946 p3146 p3156 p3379 p3452 p4278 p4669 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h48416 : (¬ p2248) ∨ (¬ p2928) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669))
    : p3379 ∨ (¬ p3146) ∨ (¬ p4669) ∨ p2922 ∨ (¬ p2248) ∨ p2417 ∨ (¬ p3156) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48416 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step78803 (p2248 p2493 p2499 p2946 p3146 p3156 p3379 p3452 p3564 p4137 p4604 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73524 : p4137 ∨ p3564)
    (h73260 : p2499 ∨ p2493)
    (h48608 : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4137) ∨ (¬ p4604))
    : p3379 ∨ (¬ p3146) ∨ (¬ p2946) ∨ (¬ p4604) ∨ p3564 ∨ (¬ p3156) ∨ p2493 ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48608 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78804 (p2088 p2992 p3146 p3177 p3189 p3857 p4360 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73566 : p4360 ∨ p3189)
    (h43771 : (¬ p2992) ∨ (¬ p3146) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p4360))
    : (¬ p2992) ∨ p2088 ∨ (¬ p3177) ∨ p3189 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43771 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78806 (p2156 p2220 p2363 p3146 p3646 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73436 : p3646 ∨ p2156)
    (h46856 : (¬ p2220) ∨ (¬ p3146) ∨ (¬ p3646) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3146) ∨ (¬ p2220) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46856 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78808 (p2363 p2563 p2598 p2619 p2911 p3055 p3146 p3201 p3644 p3698 p3876 p4110 p4133 p4347 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73560 : p4347 ∨ p2363)
    (h73350 : p3055 ∨ p2598)
    (h73516 : p4110 ∨ p2563)
    (h73434 : p3644 ∨ p2911)
    (h57508 : (¬ p2619) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3698) ∨ (¬ p3876) ∨ (¬ p4110) ∨ (¬ p4133) ∨ (¬ p4347))
    : (¬ p2619) ∨ p3201 ∨ (¬ p4133) ∨ p2363 ∨ (¬ p3146) ∨ (¬ p3698) ∨ p2598 ∨ p2563 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3698 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h57508 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u13))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step78811 (p2230 p2373 p2449 p2685 p2696 p3146 p3365 p3572 p3947 p4419 p4669 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h52128 : (¬ p2230) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3947) ∨ (¬ p4419) ∨ (¬ p4669))
    : p2449 ∨ p2685 ∨ (¬ p4419) ∨ (¬ p2373) ∨ (¬ p3146) ∨ (¬ p2230) ∨ p2696 ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2685) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4419 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h52128 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78815 (p2220 p2363 p2911 p2922 p2928 p3146 p3379 p3452 p3644 p4133 p4347 p4521 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h73560 : p4347 ∨ p2363)
    (h73434 : p3644 ∨ p2911)
    (h42437 : (¬ p2220) ∨ (¬ p2928) ∨ (¬ p3146) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4521))
    : p3379 ∨ (¬ p3146) ∨ p2922 ∨ (¬ p4133) ∨ (¬ p2220) ∨ p2363 ∨ (¬ p4521) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42437 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step78818 (p2417 p2598 p2946 p3055 p3146 p3156 p3201 p3876 p4278 p4669 p4786 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h73486 : p3876 ∨ p3201)
    (h41187 : (¬ p2946) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4786))
    : (¬ p2946) ∨ p2417 ∨ (¬ p4669) ∨ (¬ p3156) ∨ p2598 ∨ (¬ p4786) ∨ p3201 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2946 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h41187 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step78822 (p2156 p2190 p2363 p2598 p2911 p2958 p3055 p3146 p3201 p3644 p3876 p4133 p4347 p4786 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h73434 : p3644 ∨ p2911)
    (h42350 : (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2958) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3876) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4786))
    : p2363 ∨ p3201 ∨ (¬ p2958) ∨ (¬ p2190) ∨ (¬ p4786) ∨ p2598 ∨ (¬ p2156) ∨ p2911 ∨ (¬ p3146) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h42350 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step78823 (p2166 p2210 p2417 p2598 p3055 p3146 p3201 p3876 p4278 p4669 p4736 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73486 : p3876 ∨ p3201)
    (h73350 : p3055 ∨ p2598)
    (h52145 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3055) ∨ (¬ p3146) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4669) ∨ (¬ p4736))
    : p2417 ∨ p3201 ∨ (¬ p2166) ∨ (¬ p3146) ∨ (¬ p4669) ∨ (¬ p4736) ∨ (¬ p2210) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52145 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step78829 (p2166 p2255 p2417 p2662 p2727 p2946 p3146 p3389 p3412 p3540 p4111 p4278 p4669 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73518 : p4111 ∨ p2727)
    (h73402 : p3540 ∨ p3389)
    (h48523 : (¬ p2166) ∨ (¬ p2255) ∨ (¬ p2662) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3412) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4669))
    : p2417 ∨ p2727 ∨ (¬ p2946) ∨ (¬ p3412) ∨ p3389 ∨ (¬ p2255) ∨ (¬ p2166) ∨ (¬ p4669) ∨ (¬ p3146) ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3412 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48523 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step78830 (p2132 p2166 p2417 p2655 p2737 p2743 p3146 p3361 p3389 p3540 p4278 p4418 p4669 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h73298 : p2743 ∨ p2737)
    (h71402 : (¬ p4418) ∨ (¬ p4278) ∨ (¬ p2655) ∨ (¬ p2132) ∨ (¬ p3146) ∨ (¬ p3540) ∨ (¬ p2166) ∨ (¬ p4669) ∨ (¬ p2743) ∨ (¬ p3361))
    : p2417 ∨ (¬ p2655) ∨ (¬ p3361) ∨ (¬ p4418) ∨ (¬ p3146) ∨ p3389 ∨ p2737 ∨ (¬ p2166) ∨ (¬ p2132) ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71402 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u2)))))))))))))))))))))

theorem step78832 (p2144 p2156 p2190 p2363 p2437 p2651 p2657 p2911 p3146 p3644 p3742 p4133 p4347 p4789 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73288 : p2657 ∨ p2651)
    (h73560 : p4347 ∨ p2363)
    (h73434 : p3644 ∨ p2911)
    (h48187 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2657) ∨ (¬ p3146) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4789))
    : p2437 ∨ p2651 ∨ (¬ p3146) ∨ (¬ p2156) ∨ (¬ p2190) ∨ p2363 ∨ (¬ p2144) ∨ (¬ p4789) ∨ (¬ p4133) ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h48187 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step78834 (p2088 p2797 p3005 p3146 p3177 p3857 p3877 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73488 : p3877 ∨ p3005)
    (h45973 : (¬ p2797) ∨ (¬ p3146) ∨ (¬ p3177) ∨ (¬ p3857) ∨ (¬ p3877))
    : p2088 ∨ p3005 ∨ (¬ p3146) ∨ (¬ p2797) ∨ (¬ p3177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45973 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78846 (p2248 p2946 p3093 p3146 p3156 p3591 p3923 p5118 p5580 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h56236 : (¬ p2248) ∨ (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3591) ∨ (¬ p3923) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ p3093 ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p5118) ∨ (¬ p3923) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56236 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step78851 (p2190 p2901 p3146 p3256 p3661 p4118 p4558 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h54929 : (¬ p2190) ∨ (¬ p2901) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4558))
    : (¬ p2190) ∨ (¬ p3661) ∨ (¬ p4558) ∨ (¬ p2901) ∨ (¬ p3146) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h54929 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78852 (p2088 p2190 p2891 p3146 p3857 p3858 p4492 p4558 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h49678 : (¬ p2190) ∨ (¬ p2891) ∨ (¬ p3146) ∨ (¬ p3857) ∨ (¬ p3858) ∨ (¬ p4492) ∨ (¬ p4558))
    : (¬ p2190) ∨ (¬ p3146) ∨ (¬ p4492) ∨ (¬ p4558) ∨ (¬ p3858) ∨ p2088 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4492 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3858 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49678 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step78853 (p2144 p2156 p2190 p2363 p2437 p3083 p3146 p3389 p3540 p4133 p4256 p4347 p4383 p4729 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73542 : p4256 ∨ p3083)
    (h73402 : p3540 ∨ p3389)
    (h50981 : (¬ p2144) ∨ (¬ p2156) ∨ (¬ p2190) ∨ (¬ p2437) ∨ (¬ p3146) ∨ (¬ p3540) ∨ (¬ p4133) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4383) ∨ (¬ p4729))
    : (¬ p2190) ∨ p2363 ∨ (¬ p4383) ∨ (¬ p2156) ∨ p3083 ∨ (¬ p3146) ∨ p3389 ∨ (¬ p4133) ∨ (¬ p2144) ∨ (¬ p4729) ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2144 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h50981 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u11))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (False.elim (r9 u9)))))))))))))))))))))))

theorem step78855 (p2619 p3146 p3256 p3661 p4118 p4241 p4885 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h55098 : (¬ p2619) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4241) ∨ (¬ p4885))
    : (¬ p3146) ∨ (¬ p2619) ∨ (¬ p4241) ∨ (¬ p4885) ∨ (¬ p3661) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4885 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55098 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step78857 (p2177 p2254 p2946 p2952 p3093 p3146 p3256 p3309 p3661 p4118 p4905 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73520 : p4118 ∨ p3256)
    (h55479 : (¬ p2177) ∨ (¬ p2254) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3146) ∨ (¬ p3309) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4905))
    : (¬ p3309) ∨ (¬ p2254) ∨ (¬ p3661) ∨ (¬ p2177) ∨ p2946 ∨ (¬ p3146) ∨ (¬ p3093) ∨ (¬ p4905) ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3256) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55479 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step78858 (p2166 p3146 p3256 p3661 p4118 p4960 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h41513 : (¬ p2166) ∨ (¬ p3146) ∨ (¬ p3661) ∨ (¬ p4118) ∨ (¬ p4960))
    : p3256 ∨ (¬ p3661) ∨ (¬ p4960) ∨ (¬ p2166) ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p3661 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41513 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78861 (p2166 p2210 p2254 p2295 p2331 p2396 p2963 p3146 p3568 p4107 p4669 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73416 : p3568 ∨ p2295)
    (h73514 : p4107 ∨ p2396)
    (h51958 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2254) ∨ (¬ p2963) ∨ (¬ p3146) ∨ (¬ p3568) ∨ (¬ p4107) ∨ (¬ p4669))
    : p2331 ∨ p2295 ∨ (¬ p2166) ∨ (¬ p2254) ∨ (¬ p3146) ∨ (¬ p2210) ∨ p2396 ∨ (¬ p4669) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51958 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78864 (p2946 p3146 p3156 p3276 p3346 p3461 p3905 p4425 p4604 p4786 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h52151 : (¬ p2946) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p3346) ∨ (¬ p3461) ∨ (¬ p3905) ∨ (¬ p4425) ∨ (¬ p4604) ∨ (¬ p4786))
    : p3276 ∨ (¬ p3146) ∨ (¬ p3905) ∨ (¬ p4786) ∨ (¬ p3156) ∨ (¬ p2946) ∨ (¬ p3461) ∨ (¬ p4604) ∨ (¬ p3346) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h52151 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u2))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u3)))))))))))))))))))

theorem step78868 (p2459 p2901 p3146 p3156 p4320 p4348 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73562 : p4348 ∨ p2459)
    (h61879 : (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4320) ∨ (¬ p4348))
    : (¬ p3156) ∨ p2901 ∨ (¬ p3146) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h61879 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78869 (p2901 p2958 p3051 p3146 p3156 p4320 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h45824 : (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3146) ∨ (¬ p3156) ∨ (¬ p4320))
    : p2901 ∨ (¬ p3156) ∨ (¬ p3146) ∨ (¬ p3051) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45824 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step78870 (p2230 p2440 p2470 p2531 p2542 p2589 p3146 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h47109 : (¬ p2470) ∨ (¬ p2531) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3146))
    : (¬ p2470) ∨ (¬ p3146) ∨ p2230 ∨ (¬ p2531) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2531 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47109 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78872 (p2532 p3146 p5057 : Prop)
    (h73898 : p5057 ∨ (¬ p3146))
    (h8477 : p2532 ∨ (¬ p5057))
    : p2532 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2532) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h8477 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78875 (p3146 p5057 p5059 : Prop)
    (h73898 : p5057 ∨ (¬ p3146))
    (h8481 : (¬ p5057) ∨ p5059)
    : (¬ p3146) ∨ p5059 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p5059) := (fun h => hn (Or.inr h));
    let u2 : p5057 := (Or.elim h73898 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h8481 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78878 (p2373 p4606 p4608 : Prop)
    (h73664 : p4606 ∨ p2373)
    (h7344 : (¬ p4606) ∨ p4608)
    : p2373 ∨ p4608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4608) := (fun h => hn (Or.inr h));
    let u2 : p4606 := (Or.elim h73664 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7344 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step78879 (p2373 p4158 p4606 : Prop)
    (h73664 : p4606 ∨ p2373)
    (h7345 : p4158 ∨ (¬ p4606))
    : p4158 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4158) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr h));
    let u2 : p4606 := (Or.elim h73664 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7345 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step78880 (p2373 p2493 p2509 p2563 p4606 p4716 : Prop)
    (h73664 : p4606 ∨ p2373)
    (h73722 : p4716 ∨ (¬ p2563))
    (h69484 : (¬ p2509) ∨ (¬ p2493) ∨ (¬ p4606) ∨ (¬ p4716))
    : p2373 ∨ (¬ p2509) ∨ (¬ p2563) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4606 := (Or.elim h73664 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4716 := (Or.elim h73722 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h69484 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78881 (p2373 p3083 p3156 p3497 p4256 p4606 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73664 : p4606 ∨ p2373)
    (h73399 : (¬ p3156) ∨ (¬ p3497))
    (h67220 : (¬ p4606) ∨ (¬ p4256) ∨ p3497 ∨ (¬ p3156))
    : (¬ p3156) ∨ p3083 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p4606 := (Or.elim h73664 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : (¬ p3497) := (Or.elim h73399 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    (Or.elim h67220 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (u5 q2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78882 (p2373 p2459 p2563 p3146 p3692 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73448 : p3692 ∨ p3146)
    (h43908 : (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880))
    : p2373 ∨ p3146 ∨ (¬ p2563) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43908 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78884 (p2373 p2427 p3051 p3146 p3556 p3692 p3880 p3904 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73490 : p3880 ∨ p2373)
    (h73448 : p3692 ∨ p3146)
    (h44779 : (¬ p2427) ∨ (¬ p3556) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3904))
    : p3051 ∨ p2373 ∨ (¬ p3904) ∨ p3146 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3904 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44779 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78885 (p2373 p2427 p2608 p2819 p2829 p3051 p3556 p3880 p4134 p4524 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73490 : p3880 ∨ p2373)
    (h72962 : p4524)
    (h52243 : (¬ p2427) ∨ (¬ p2608) ∨ (¬ p2819) ∨ (¬ p2829) ∨ (¬ p3556) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4524))
    : p3051 ∨ p2373 ∨ (¬ p2829) ∨ (¬ p2819) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p4134) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4524 := h72962;
    (Or.elim h52243 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u9)))))))))))))))))

theorem step78889 (p2363 p2373 p2406 p2459 p2641 p2668 p3238 p3379 p3452 p3880 p4348 p4905 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h73562 : p4348 ∨ p2459)
    (h54102 : (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905))
    : p2406 ∨ p3379 ∨ (¬ p2363) ∨ (¬ p4905) ∨ (¬ p2641) ∨ p2373 ∨ (¬ p2668) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54102 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78892 (p2373 p2427 p3747 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h20076 : (¬ p2427) ∨ (¬ p3747) ∨ (¬ p3880))
    : (¬ p3747) ∨ p2373 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3747 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20076 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78898 (p2373 p2406 p3146 p3238 p3379 p3452 p3692 p3880 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73448 : p3692 ∨ p3146)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h43534 : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3692) ∨ (¬ p3880))
    : p3379 ∨ p3146 ∨ p2406 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43534 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step78899 (p2230 p2241 p2373 p2589 p2641 p3146 p3323 p3692 p3880 p4330 p5193 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h50275 : (¬ p2241) ∨ (¬ p2589) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4330) ∨ (¬ p5193))
    : (¬ p3323) ∨ p3146 ∨ (¬ p4330) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p2641) ∨ p2373 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50275 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step78901 (p2373 p2427 p3246 p3880 p4132 p4668 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h49775 : (¬ p2427) ∨ (¬ p3246) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4668))
    : (¬ p3246) ∨ p2373 ∨ (¬ p4132) ∨ (¬ p4668) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h49775 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78903 (p2363 p2373 p2563 p3146 p3692 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73448 : p3692 ∨ p3146)
    (h43375 : (¬ p2363) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p3880))
    : p2373 ∨ p3146 ∨ (¬ p2563) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43375 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78904 (p2177 p2373 p2427 p3880 p4132 p4556 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h50154 : (¬ p2177) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4556))
    : (¬ p2427) ∨ (¬ p4132) ∨ (¬ p4556) ∨ p2373 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50154 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78905 (p2264 p2373 p2427 p3880 p4132 p4362 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h64694 : (¬ p2264) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p4362))
    : (¬ p2427) ∨ (¬ p2264) ∨ (¬ p4132) ∨ (¬ p4362) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64694 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78906 (p2341 p2373 p2427 p3880 p4132 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h68265 : (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4132) ∨ (¬ p2341))
    : (¬ p2341) ∨ p2373 ∨ (¬ p4132) ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h68265 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78908 (p2088 p2373 p2532 p2982 p3857 p3880 p4529 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73490 : p3880 ∨ p2373)
    (h42146 : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3857) ∨ (¬ p3880) ∨ (¬ p4529))
    : p2088 ∨ (¬ p2532) ∨ (¬ p4529) ∨ (¬ p2982) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4529 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42146 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78909 (p2373 p2532 p2982 p3073 p3880 p4261 p4494 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73490 : p3880 ∨ p2373)
    (h63955 : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4261) ∨ (¬ p4494))
    : (¬ p2982) ∨ p3073 ∨ (¬ p2532) ∨ p2373 ∨ (¬ p4494) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4494 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63955 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78911 (p2230 p2373 p2459 p2589 p3146 p3692 p3880 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h44763 : (¬ p2459) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3880))
    : p3146 ∨ p2373 ∨ (¬ p2459) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44763 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78912 (p2190 p2373 p2563 p3880 p4110 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73515 : (¬ p2563) ∨ (¬ p4110))
    (h6279 : (¬ p2190) ∨ (¬ p3880) ∨ p4110)
    : (¬ p2190) ∨ p2373 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p4110) := (Or.elim h73515 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6279 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u4 r1)))))))

theorem step78920 (p2145 p2156 p2373 p2563 p2685 p2807 p3005 p3572 p3646 p3880 p4117 p5063 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73420 : p3572 ∨ p2685)
    (h73436 : p3646 ∨ p2156)
    (h55295 : (¬ p2145) ∨ (¬ p2563) ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p3572) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4117) ∨ (¬ p5063))
    : p2373 ∨ (¬ p2145) ∨ p2685 ∨ p2156 ∨ (¬ p2807) ∨ (¬ p3005) ∨ (¬ p2563) ∨ (¬ p4117) ∨ (¬ p5063) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4117 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55295 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step78921 (p2373 p2563 p3204 p3309 p3743 p3880 p4506 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h71403 : (¬ p3204) ∨ (¬ p4506) ∨ (¬ p3743) ∨ (¬ p3880) ∨ (¬ p3309) ∨ (¬ p2563))
    : p2373 ∨ (¬ p3309) ∨ (¬ p4506) ∨ (¬ p3743) ∨ (¬ p3204) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3743 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71403 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step78922 (p2373 p3146 p3256 p3692 p3880 p4237 p4705 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73448 : p3692 ∨ p3146)
    (h41999 : (¬ p3256) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4237) ∨ (¬ p4705))
    : (¬ p3256) ∨ (¬ p4237) ∨ p2373 ∨ (¬ p4705) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4237 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41999 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step78923 (p2373 p2406 p3156 p3238 p3413 p3880 p4811 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h48791 : (¬ p3156) ∨ (¬ p3238) ∨ (¬ p3413) ∨ (¬ p3880) ∨ (¬ p4811))
    : (¬ p3156) ∨ (¬ p3413) ∨ p2406 ∨ p2373 ∨ (¬ p4811) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48791 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78925 (p2373 p3156 p3879 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h5740 : (¬ p3156) ∨ (¬ p3879) ∨ (¬ p3880))
    : (¬ p3879) ∨ (¬ p3156) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3879 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h5740 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78927 (p2373 p2563 p3325 p3880 p3979 p4115 p5590 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h46694 : (¬ p2563) ∨ (¬ p3325) ∨ (¬ p3880) ∨ (¬ p3979) ∨ (¬ p4115) ∨ (¬ p5590))
    : (¬ p5590) ∨ (¬ p3979) ∨ (¬ p3325) ∨ (¬ p4115) ∨ (¬ p2563) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4115 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46694 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step78930 (p2220 p2373 p2406 p3238 p3880 p4399 p5194 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h49536 : (¬ p2220) ∨ (¬ p3238) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p5194))
    : (¬ p2220) ∨ (¬ p4399) ∨ p2406 ∨ p2373 ∨ (¬ p5194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49536 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78931 (p2220 p2331 p2373 p2396 p2563 p2963 p3366 p3519 p3791 p3880 p4067 p4107 p4236 p4376 p4391 p4399 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73490 : p3880 ∨ p2373)
    (h73338 : p2963 ∨ p2331)
    (h47187 : (¬ p2220) ∨ (¬ p2563) ∨ (¬ p2963) ∨ (¬ p3366) ∨ (¬ p3519) ∨ (¬ p3791) ∨ (¬ p3880) ∨ (¬ p4067) ∨ (¬ p4107) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4391) ∨ (¬ p4399))
    : (¬ p3791) ∨ (¬ p4399) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p2563) ∨ (¬ p2220) ∨ (¬ p4391) ∨ (¬ p3519) ∨ (¬ p4067) ∨ p2396 ∨ p2373 ∨ (¬ p4376) ∨ p2331 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))));
    let u11 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))));
    let u12 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))));
    let u13 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    let u14 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    let u15 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u12 r0))));
    (Or.elim h47187 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u15))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u14))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u13))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u2))) (fun r9 => (Or.elim r9 (fun q10 => (False.elim (q10 u11))) (fun r10 => (Or.elim r10 (fun q11 => (False.elim (q11 u6))) (fun r11 => (False.elim (r11 u1)))))))))))))))))))))))))))

theorem step78932 (p2220 p2373 p2427 p2608 p3005 p3519 p3755 p3830 p3834 p3847 p3877 p3880 p4376 p4399 : Prop)
    (h73474 : p3834 ∨ p3830)
    (h73490 : p3880 ∨ p2373)
    (h73488 : p3877 ∨ p3005)
    (h47184 : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p2608) ∨ (¬ p3519) ∨ (¬ p3755) ∨ (¬ p3834) ∨ (¬ p3847) ∨ (¬ p3877) ∨ (¬ p3880) ∨ (¬ p4376) ∨ (¬ p4399))
    : (¬ p3755) ∨ p3830 ∨ (¬ p4399) ∨ (¬ p3847) ∨ (¬ p3519) ∨ (¬ p2427) ∨ (¬ p2220) ∨ p2373 ∨ p3005 ∨ (¬ p4376) ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3830) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3847 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p3834 := (Or.elim h73474 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h47184 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u13))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u9))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step78933 (p2230 p2373 p2573 p2589 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h67013 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3880))
    : (¬ p2573) ∨ p2373 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h67013 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u3)))))))

theorem step78936 (p2373 p2440 p3016 p3880 p4203 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h69486 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3880) ∨ (¬ p4203))
    : (¬ p3016) ∨ (¬ p2440) ∨ (¬ p4203) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69486 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step78937 (p2252 p2373 p2440 p2608 p2651 p2657 p2750 p3399 p3527 p3880 p3954 p4905 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73498 : p3954 ∨ p2608)
    (h73490 : p3880 ∨ p2373)
    (h41579 : (¬ p2252) ∨ (¬ p2440) ∨ (¬ p2657) ∨ (¬ p2750) ∨ (¬ p3399) ∨ (¬ p3527) ∨ (¬ p3880) ∨ (¬ p3954) ∨ (¬ p4905))
    : (¬ p2750) ∨ p2651 ∨ p2608 ∨ (¬ p3527) ∨ (¬ p2440) ∨ (¬ p4905) ∨ (¬ p3399) ∨ (¬ p2252) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2750 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3527 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h41579 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step78942 (p2373 p2850 p3146 p3266 p3684 p3692 p3880 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73442 : p3684 ∨ p2850)
    (h46051 : (¬ p3684) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4444))
    : p3266 ∨ p3146 ∨ p2373 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46051 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78943 (p2230 p2241 p2264 p2373 p2589 p2996 p3027 p3146 p3266 p3692 p3880 p4444 p5193 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73490 : p3880 ∨ p2373)
    (h73340 : p3027 ∨ p2996)
    (h73284 : p2589 ∨ p2230)
    (h73448 : p3692 ∨ p3146)
    (h50421 : (¬ p2241) ∨ (¬ p2264) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4444) ∨ (¬ p5193))
    : p3266 ∨ (¬ p2264) ∨ p2373 ∨ (¬ p2241) ∨ p2996 ∨ (¬ p5193) ∨ p2230 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50421 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step78944 (p2166 p2373 p2563 p2598 p3055 p3366 p3371 p3880 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73490 : p3880 ∨ p2373)
    (h47257 : (¬ p2166) ∨ (¬ p2563) ∨ (¬ p3055) ∨ (¬ p3366) ∨ (¬ p3371) ∨ (¬ p3880))
    : (¬ p3371) ∨ p2598 ∨ (¬ p2166) ∨ p2373 ∨ (¬ p3366) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3371 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47257 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step78945 (p2210 p2373 p3146 p3379 p3555 p3692 p3880 p4034 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h47709 : (¬ p3379) ∨ (¬ p3555) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4034))
    : p2210 ∨ p3146 ∨ (¬ p3379) ∨ p2373 ∨ (¬ p4034) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4034 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47709 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78950 (p2373 p2982 p3115 p3136 p3880 p4208 p4315 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73490 : p3880 ∨ p2373)
    (h73550 : p4315 ∨ p3136)
    (h60139 : (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4315))
    : (¬ p2982) ∨ p3115 ∨ p2373 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60139 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78951 (p2373 p2982 p3880 p4335 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h38570 : (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4335))
    : (¬ p2982) ∨ (¬ p4335) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4335 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h38570 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step78955 (p2220 p2373 p2493 p2573 p2579 p3880 p4399 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73274 : p2579 ∨ p2573)
    (h45458 : (¬ p2220) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399))
    : (¬ p2220) ∨ (¬ p4399) ∨ p2373 ∨ p2573 ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45458 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step78956 (p2220 p2373 p2573 p2579 p3880 p4399 p4715 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73274 : p2579 ∨ p2573)
    (h53239 : (¬ p2220) ∨ (¬ p2579) ∨ (¬ p3880) ∨ (¬ p4399) ∨ (¬ p4715))
    : (¬ p2220) ∨ (¬ p4399) ∨ (¬ p4715) ∨ p2373 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53239 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78957 (p2373 p2440 p2651 p2657 p3146 p3692 p3880 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73288 : p2657 ∨ p2651)
    (h73490 : p3880 ∨ p2373)
    (h46838 : (¬ p2440) ∨ (¬ p2657) ∨ (¬ p3692) ∨ (¬ p3880))
    : p3146 ∨ p2651 ∨ p2373 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46838 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step78960 (p2156 p2220 p2373 p2427 p3646 p3880 p4558 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73436 : p3646 ∨ p2156)
    (h52131 : (¬ p2220) ∨ (¬ p2427) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4558))
    : (¬ p2220) ∨ p2373 ∨ (¬ p4558) ∨ (¬ p2427) ∨ p2156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52131 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78963 (p2230 p2373 p2589 p2662 p2727 p3146 p3692 p3880 p4111 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73518 : p4111 ∨ p2727)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h55718 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4111))
    : p3146 ∨ p2727 ∨ (¬ p2662) ∨ p2230 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55718 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step78965 (p2230 p2373 p2589 p2630 p2662 p2810 p3146 p3692 p3880 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73316 : p2810 ∨ p2630)
    (h73490 : p3880 ∨ p2373)
    (h45982 : (¬ p2589) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3692) ∨ (¬ p3880))
    : (¬ p2662) ∨ p3146 ∨ p2230 ∨ p2630 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2662 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45982 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step78967 (p2230 p2241 p2373 p2449 p2589 p2996 p3027 p3146 p3692 p3880 p3950 p5193 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73340 : p3027 ∨ p2996)
    (h73490 : p3880 ∨ p2373)
    (h51411 : (¬ p2241) ∨ (¬ p2449) ∨ (¬ p2589) ∨ (¬ p3027) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3950) ∨ (¬ p5193))
    : p3146 ∨ (¬ p3950) ∨ (¬ p2449) ∨ (¬ p5193) ∨ p2230 ∨ (¬ p2241) ∨ p2996 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h51411 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step78970 (p2373 p3073 p3146 p3692 p3880 p4496 p4632 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h48376 : (¬ p3073) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p4496) ∨ (¬ p4632))
    : p3146 ∨ (¬ p3073) ∨ (¬ p4632) ∨ p2373 ∨ (¬ p4496) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p3073 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4496 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48376 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78972 (p2230 p2373 p2589 p2608 p3146 p3347 p3399 p3631 p3692 p3880 p3950 p3954 : Prop)
    (h73498 : p3954 ∨ p2608)
    (h73448 : p3692 ∨ p3146)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h71404 : (¬ p3399) ∨ (¬ p3347) ∨ (¬ p2589) ∨ (¬ p3692) ∨ (¬ p3950) ∨ (¬ p3954) ∨ (¬ p3631) ∨ (¬ p3880))
    : p2608 ∨ p3146 ∨ p2373 ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p3347) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h71404 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step78976 (p2373 p2440 p2946 p3156 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h54568 : (¬ p2440) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880))
    : (¬ p2440) ∨ (¬ p3156) ∨ p2373 ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54568 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step78977 (p2373 p2651 p2657 p2946 p3156 p3880 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73490 : p3880 ∨ p2373)
    (h45241 : (¬ p2657) ∨ (¬ p2946) ∨ (¬ p3156) ∨ (¬ p3880))
    : (¬ p3156) ∨ (¬ p2946) ∨ p2651 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45241 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step78980 (p2166 p2192 p2373 p2427 p3880 p4173 p4558 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73528 : p4173 ∨ p2192)
    (h56966 : (¬ p2166) ∨ (¬ p2427) ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4558))
    : (¬ p2166) ∨ p2373 ∨ p2192 ∨ (¬ p2427) ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56966 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step78986 (p2373 p2532 p2982 p3256 p3880 p4118 p5063 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73490 : p3880 ∨ p2373)
    (h49767 : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p4118) ∨ (¬ p5063))
    : p3256 ∨ (¬ p2982) ∨ (¬ p5063) ∨ p2373 ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49767 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78988 (p2373 p2406 p2651 p2657 p3166 p3238 p3487 p3880 p5063 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h60111 : (¬ p2657) ∨ (¬ p3166) ∨ (¬ p3238) ∨ (¬ p3487) ∨ (¬ p3880) ∨ (¬ p5063))
    : (¬ p3166) ∨ p2651 ∨ (¬ p5063) ∨ p2373 ∨ (¬ p3487) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3487 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h60111 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step78989 (p2373 p2532 p2982 p3880 p5118 p5568 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h56967 : (¬ p2532) ∨ (¬ p2982) ∨ (¬ p3880) ∨ (¬ p5118) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p5118) ∨ p2373 ∨ (¬ p2532) ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56967 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step78991 (p2373 p3115 p3156 p3880 p4208 p4322 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73490 : p3880 ∨ p2373)
    (h59234 : (¬ p3156) ∨ (¬ p3880) ∨ (¬ p4208) ∨ (¬ p4322))
    : (¬ p4322) ∨ p3115 ∨ p2373 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3115) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h59234 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step78994 (p2373 p3016 p3156 p3413 p3574 p3880 p4715 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73422 : p3574 ∨ p3016)
    (h62561 : (¬ p3156) ∨ (¬ p3413) ∨ (¬ p3574) ∨ (¬ p3880) ∨ (¬ p4715))
    : (¬ p3156) ∨ (¬ p3413) ∨ (¬ p4715) ∨ p2373 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62561 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step78996 (p2139 p2220 p2264 p2274 p2373 p2553 p2685 p2696 p3097 p3365 p3553 p3572 p3660 p3880 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h73490 : p3880 ∨ p2373)
    (h73352 : p3097 ∨ p2274)
    (h73420 : p3572 ∨ p2685)
    (h73390 : p3365 ∨ p2696)
    (h55921 : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3365) ∨ (¬ p3553) ∨ (¬ p3572) ∨ (¬ p3660) ∨ (¬ p3880))
    : (¬ p3660) ∨ p2264 ∨ (¬ p2553) ∨ (¬ p2220) ∨ p2373 ∨ p2274 ∨ p2685 ∨ (¬ p2139) ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3660 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2264) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u13 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55921 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u13))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (False.elim (r7 u10)))))))))))))))))))

theorem step78997 (p2139 p2220 p2373 p2449 p2685 p2696 p2982 p3365 p3572 p3880 p3947 p4395 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73390 : p3365 ∨ p2696)
    (h73490 : p3880 ∨ p2373)
    (h73420 : p3572 ∨ p2685)
    (h55248 : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p2982) ∨ (¬ p3365) ∨ (¬ p3572) ∨ (¬ p3880) ∨ (¬ p3947) ∨ (¬ p4395))
    : p2449 ∨ (¬ p2982) ∨ (¬ p2139) ∨ (¬ p2220) ∨ p2696 ∨ p2373 ∨ p2685 ∨ (¬ p4395) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2685) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3572 := (Or.elim h73420 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55248 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step78998 (p2331 p2363 p2373 p2598 p2668 p2850 p3055 p3684 p3880 p4786 p5568 : Prop)
    (h73442 : p3684 ∨ p2850)
    (h73490 : p3880 ∨ p2373)
    (h73350 : p3055 ∨ p2598)
    (h47022 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3055) ∨ (¬ p3684) ∨ (¬ p3880) ∨ (¬ p4786) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p2668) ∨ (¬ p2363) ∨ p2850 ∨ p2373 ∨ (¬ p2331) ∨ p2598 ∨ (¬ p4786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h47022 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step78999 (p2230 p2241 p2247 p2373 p2589 p2744 p3146 p3366 p3399 p3631 p3692 p3880 p3905 p3950 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73284 : p2589 ∨ p2230)
    (h73490 : p3880 ∨ p2373)
    (h73226 : p2247 ∨ p2241)
    (h56823 : (¬ p2247) ∨ (¬ p2589) ∨ (¬ p2744) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3631) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3905) ∨ (¬ p3950))
    : (¬ p3399) ∨ p3146 ∨ (¬ p3366) ∨ p2230 ∨ (¬ p3905) ∨ p2373 ∨ p2241 ∨ (¬ p3950) ∨ (¬ p3631) ∨ (¬ p2744) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3631 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u12 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56823 (fun q0 => (False.elim (q0 u13))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u4))) (fun r8 => (False.elim (r8 u7)))))))))))))))))))))

theorem step79001 (p2373 p2982 p3136 p3755 p3880 p4035 p4040 : Prop)
    (h73506 : p4035 ∨ p3755)
    (h73490 : p3880 ∨ p2373)
    (h46460 : (¬ p2982) ∨ (¬ p3136) ∨ (¬ p3880) ∨ (¬ p4035) ∨ (¬ p4040))
    : (¬ p4040) ∨ (¬ p3136) ∨ p3755 ∨ (¬ p2982) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4040 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3755) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4035 := (Or.elim h73506 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46460 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79003 (p2373 p2563 p2992 p3156 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h45048 : (¬ p2563) ∨ (¬ p2992) ∨ (¬ p3156) ∨ (¬ p3880))
    : p2373 ∨ (¬ p3156) ∨ (¬ p2992) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45048 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79004 (p2156 p2220 p2274 p2373 p3097 p3646 p3880 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73490 : p3880 ∨ p2373)
    (h73352 : p3097 ∨ p2274)
    (h45266 : (¬ p2220) ∨ (¬ p3097) ∨ (¬ p3646) ∨ (¬ p3880))
    : p2156 ∨ (¬ p2220) ∨ p2373 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45266 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79005 (p2166 p2274 p2373 p2553 p3097 p3660 p3880 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73490 : p3880 ∨ p2373)
    (h47259 : (¬ p2166) ∨ (¬ p2553) ∨ (¬ p3097) ∨ (¬ p3660) ∨ (¬ p3880))
    : (¬ p2553) ∨ p2274 ∨ p2373 ∨ (¬ p3660) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47259 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79006 (p2166 p2373 p2563 p3379 p3880 p3948 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h43174 : (¬ p2166) ∨ (¬ p2563) ∨ (¬ p3379) ∨ (¬ p3880) ∨ (¬ p3948))
    : p2373 ∨ (¬ p2166) ∨ (¬ p3379) ∨ (¬ p3948) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3948 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h43174 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79007 (p2098 p2145 p2156 p2373 p2459 p2563 p3609 p3646 p3880 p4348 p4905 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73490 : p3880 ∨ p2373)
    (h73436 : p3646 ∨ p2156)
    (h62744 : (¬ p2098) ∨ (¬ p2145) ∨ (¬ p2563) ∨ (¬ p3609) ∨ (¬ p3646) ∨ (¬ p3880) ∨ (¬ p4348) ∨ (¬ p4905))
    : (¬ p3609) ∨ p2459 ∨ p2373 ∨ (¬ p2098) ∨ (¬ p2563) ∨ p2156 ∨ (¬ p2145) ∨ (¬ p4905) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2145 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62744 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step79008 (p2192 p2363 p2373 p2563 p3880 p4173 p4347 p4506 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73528 : p4173 ∨ p2192)
    (h73490 : p3880 ∨ p2373)
    (h48308 : (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4173) ∨ (¬ p4347) ∨ (¬ p4506))
    : p2363 ∨ p2192 ∨ (¬ p2563) ∨ (¬ p4506) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2192) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48308 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79011 (p2295 p2373 p2563 p2668 p3568 p3880 p4506 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73416 : p3568 ∨ p2295)
    (h48803 : (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3880) ∨ (¬ p4506))
    : p2373 ∨ (¬ p2668) ∨ p2295 ∨ (¬ p2563) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48803 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79012 (p2373 p2563 p3125 p3880 p4506 p4603 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h56404 : (¬ p2563) ∨ (¬ p3125) ∨ (¬ p3880) ∨ (¬ p4506) ∨ (¬ p4603))
    : (¬ p3125) ∨ p2373 ∨ (¬ p4506) ∨ (¬ p4603) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4603 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56404 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79014 (p2373 p2383 p2563 p3880 p4489 p4506 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h49218 : (¬ p2383) ∨ (¬ p2563) ∨ (¬ p3880) ∨ (¬ p4489) ∨ (¬ p4506))
    : p2373 ∨ (¬ p2383) ∨ (¬ p2563) ∨ (¬ p4489) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49218 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79015 (p2230 p2373 p2396 p2589 p3093 p3146 p3309 p3692 p3880 p3905 p3950 p4736 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h73284 : p2589 ∨ p2230)
    (h73448 : p3692 ∨ p3146)
    (h55813 : (¬ p2396) ∨ (¬ p2589) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3692) ∨ (¬ p3880) ∨ (¬ p3905) ∨ (¬ p3950) ∨ (¬ p4736))
    : (¬ p3309) ∨ (¬ p2396) ∨ p2373 ∨ (¬ p3093) ∨ p2230 ∨ (¬ p3905) ∨ p3146 ∨ (¬ p3950) ∨ (¬ p4736) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4736 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h55813 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step79017 (p2220 p2274 p2373 p2563 p3880 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h53925 : (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2563) ∨ (¬ p3880))
    : p2373 ∨ (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53925 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79019 (p2373 p2563 p2668 p3880 p4446 p4560 p4993 : Prop)
    (h73490 : p3880 ∨ p2373)
    (h72955 : p4560)
    (h51218 : (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3880) ∨ (¬ p4446) ∨ (¬ p4560) ∨ (¬ p4993))
    : p2373 ∨ (¬ p4446) ∨ (¬ p4993) ∨ (¬ p2668) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4993 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4560 := h72955;
    (Or.elim h51218 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79023 (p2284 p2528 p3146 p3156 p3497 p3692 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73448 : p3692 ∨ p3146)
    (h44220 : (¬ p2284) ∨ (¬ p2528) ∨ (¬ p3497) ∨ (¬ p3692))
    : p3156 ∨ p3146 ∨ (¬ p2284) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44220 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79024 (p2284 p2363 p3146 p3156 p3497 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h45906 : (¬ p2284) ∨ (¬ p2363) ∨ (¬ p3497) ∨ (¬ p3692))
    : p3146 ∨ p3156 ∨ (¬ p2284) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45906 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79025 (p2190 p2284 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h5078 : (¬ p2190) ∨ (¬ p2284) ∨ (¬ p3497))
    : (¬ p2190) ∨ p3156 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2190 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h5078 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u3)))))))

theorem step79026 (p2220 p2284 p3051 p3156 p3497 p3556 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73414 : p3556 ∨ p3051)
    (h44601 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3556))
    : p3156 ∨ (¬ p2220) ∨ (¬ p2284) ∨ p3051 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44601 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79027 (p2220 p2284 p3051 p3156 p3497 p3556 p4555 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73414 : p3556 ∨ p3051)
    (h48082 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4555))
    : p3156 ∨ (¬ p2220) ∨ p3051 ∨ (¬ p4555) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48082 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79029 (p2373 p2651 p2946 p2952 p3156 p3497 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h44202 : (¬ p2373) ∨ (¬ p2651) ∨ (¬ p2952) ∨ (¬ p3497))
    : p2946 ∨ p3156 ∨ (¬ p2373) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44202 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79030 (p2737 p2743 p2946 p2952 p3146 p3156 p3361 p3497 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h73298 : p2743 ∨ p2737)
    (h46821 : (¬ p2743) ∨ (¬ p2952) ∨ (¬ p3361) ∨ (¬ p3497) ∨ (¬ p3692))
    : p3146 ∨ p3156 ∨ (¬ p3361) ∨ p2946 ∨ p2737 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46821 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79032 (p2220 p2331 p2946 p2952 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h57578 : (¬ p2220) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3497))
    : p3156 ∨ p2946 ∨ (¬ p2331) ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h57578 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79033 (p2274 p2284 p3156 p3497 p4506 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h71406 : (¬ p3497) ∨ (¬ p2284) ∨ (¬ p2274) ∨ (¬ p4506))
    : p3156 ∨ (¬ p2274) ∨ (¬ p2284) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71406 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step79034 (p2459 p2901 p3146 p3156 p3497 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h46088 : (¬ p2459) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3692))
    : (¬ p2901) ∨ p3146 ∨ (¬ p2459) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46088 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79035 (p2901 p3051 p3146 p3156 p3497 p3556 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73414 : p3556 ∨ p3051)
    (h73400 : p3497 ∨ p3156)
    (h47945 : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p3692))
    : (¬ p2901) ∨ p3146 ∨ p3051 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47945 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79036 (p2220 p2427 p2901 p3156 p3370 p3497 p4235 p4632 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73400 : p3497 ∨ p3156)
    (h56444 : (¬ p2220) ∨ (¬ p2901) ∨ (¬ p3370) ∨ (¬ p3497) ∨ (¬ p4235) ∨ (¬ p4632))
    : (¬ p2901) ∨ (¬ p3370) ∨ (¬ p4632) ∨ p2427 ∨ (¬ p2220) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4632 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56444 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79037 (p2870 p2901 p3146 p3156 p3497 p3692 p4244 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h73540 : p4244 ∨ p2870)
    (h59450 : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4244))
    : (¬ p2901) ∨ p3146 ∨ p3156 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59450 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79038 (p2192 p2210 p2284 p3156 p3497 p3555 p4173 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73412 : p3555 ∨ p2210)
    (h73528 : p4173 ∨ p2192)
    (h46244 : (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3555) ∨ (¬ p4173))
    : p3156 ∨ p2210 ∨ (¬ p2284) ∨ p2192 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2210) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46244 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79039 (p2230 p2284 p2373 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h44915 : (¬ p2230) ∨ (¬ p2284) ∨ (¬ p2373) ∨ (¬ p3497))
    : (¬ p2284) ∨ p3156 ∨ (¬ p2373) ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44915 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79040 (p2373 p2563 p2946 p2952 p3156 p3497 p4110 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h73516 : p4110 ∨ p2563)
    (h46840 : (¬ p2373) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p4110))
    : p2946 ∨ p3156 ∨ (¬ p2373) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46840 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79045 (p2901 p3156 p3497 p4129 p4132 p5564 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h42637 : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4129) ∨ (¬ p4132) ∨ (¬ p5564))
    : (¬ p4129) ∨ (¬ p5564) ∨ p3156 ∨ (¬ p2901) ∨ (¬ p4132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42637 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step79051 (p2156 p2901 p3051 p3156 p3497 p3556 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h73400 : p3497 ∨ p3156)
    (h43030 : (¬ p2156) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3556))
    : p3051 ∨ p3156 ∨ (¬ p2901) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43030 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79053 (p2417 p2901 p3156 p3246 p3497 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73400 : p3497 ∨ p3156)
    (h58968 : (¬ p2901) ∨ (¬ p3246) ∨ (¬ p3497) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3246) ∨ (¬ p2901) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58968 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79054 (p2166 p2210 p2901 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h64038 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2901) ∨ (¬ p3497))
    : (¬ p2901) ∨ p3156 ∨ (¬ p2166) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h64038 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79055 (p2166 p2241 p2284 p3156 p3497 p4365 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h55280 : (¬ p2166) ∨ (¬ p2241) ∨ (¬ p2284) ∨ (¬ p3497) ∨ (¬ p4365))
    : p3156 ∨ (¬ p2241) ∨ (¬ p4365) ∨ (¬ p2166) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55280 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79056 (p2166 p2210 p2284 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h45846 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p2284) ∨ (¬ p3497))
    : p3156 ∨ (¬ p2210) ∨ (¬ p2166) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45846 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79062 (p2331 p2946 p2952 p3156 p3497 p3986 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h69487 : (¬ p2952) ∨ (¬ p3986) ∨ (¬ p3497) ∨ (¬ p2331))
    : (¬ p2331) ∨ p3156 ∨ (¬ p3986) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h69487 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79064 (p2619 p2860 p2946 p2952 p3156 p3497 p3758 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h42885 : (¬ p2619) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3758))
    : p2860 ∨ (¬ p2619) ∨ p3156 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42885 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79065 (p2284 p2860 p3146 p3156 p3497 p3692 p3758 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73448 : p3692 ∨ p3146)
    (h73456 : p3758 ∨ p2860)
    (h58134 : (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3758))
    : p3156 ∨ p3146 ∨ p2860 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h58134 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79067 (p2352 p2493 p2901 p3051 p3156 p3379 p3497 p3556 p4134 p4524 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h72962 : p4524)
    (h73414 : p3556 ∨ p3051)
    (h52085 : (¬ p2352) ∨ (¬ p2493) ∨ (¬ p2901) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3556) ∨ (¬ p4134) ∨ (¬ p4524))
    : (¬ p2901) ∨ p3156 ∨ (¬ p3379) ∨ p3051 ∨ (¬ p2352) ∨ (¬ p4134) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p4524 := h72962;
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52085 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step79069 (p2241 p2247 p2284 p3156 p3449 p3497 p4446 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73226 : p2247 ∨ p2241)
    (h46589 : (¬ p2247) ∨ (¬ p2284) ∨ (¬ p3449) ∨ (¬ p3497) ∨ (¬ p4446))
    : p3156 ∨ p2241 ∨ (¬ p4446) ∨ (¬ p2284) ∨ (¬ p3449) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2241) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4446 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46589 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79072 (p2220 p2274 p2307 p2313 p3156 p3497 p4198 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73238 : p2313 ∨ p2307)
    (h48471 : (¬ p2220) ∨ (¬ p2274) ∨ (¬ p2313) ∨ (¬ p3497) ∨ (¬ p4198))
    : p3156 ∨ (¬ p2274) ∨ (¬ p2220) ∨ (¬ p4198) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4198 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48471 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79073 (p2284 p2352 p3156 p3497 p4506 p4718 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h60936 : (¬ p2284) ∨ (¬ p2352) ∨ (¬ p3497) ∨ (¬ p4506) ∨ (¬ p4718))
    : (¬ p2352) ∨ (¬ p2284) ∨ p3156 ∨ (¬ p4718) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60936 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79076 (p2363 p2946 p2952 p3146 p3156 p3497 p3692 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h56680 : (¬ p2363) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692))
    : p3146 ∨ p2946 ∨ (¬ p2363) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56680 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79079 (p2459 p3136 p3146 p3156 p3497 p3692 p4315 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h73550 : p4315 ∨ p3136)
    (h44799 : (¬ p2459) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4315))
    : p3146 ∨ p3156 ∨ (¬ p2459) ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44799 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79080 (p2341 p2901 p3156 p3497 p3575 p4132 p4647 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h49371 : (¬ p2341) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p3575) ∨ (¬ p4132) ∨ (¬ p4647))
    : (¬ p2901) ∨ (¬ p2341) ∨ (¬ p4647) ∨ (¬ p3575) ∨ (¬ p4132) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3575 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49371 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79086 (p2295 p2307 p2313 p2785 p3156 p3497 p4185 p4336 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73400 : p3497 ∨ p3156)
    (h69489 : (¬ p3497) ∨ (¬ p4185) ∨ (¬ p2313) ∨ (¬ p2295) ∨ (¬ p4336) ∨ (¬ p2785))
    : (¬ p2295) ∨ p2307 ∨ (¬ p4185) ∨ (¬ p4336) ∨ (¬ p2785) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4185 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2785 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h69489 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step79087 (p2528 p2532 p2534 p3115 p3156 p3497 p4158 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73400 : p3497 ∨ p3156)
    (h55170 : (¬ p2532) ∨ (¬ p2534) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p4158))
    : (¬ p3115) ∨ p2528 ∨ (¬ p4158) ∨ p3156 ∨ (¬ p2532) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4158 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2532 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55170 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79089 (p2177 p2901 p3156 p3497 p4132 p4556 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h50152 : (¬ p2177) ∨ (¬ p2901) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4556))
    : (¬ p2901) ∨ (¬ p4132) ∨ (¬ p4556) ∨ p3156 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50152 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79090 (p2284 p2383 p3156 p3497 p4489 p4506 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h50482 : (¬ p2284) ∨ (¬ p2383) ∨ (¬ p3497) ∨ (¬ p4489) ∨ (¬ p4506))
    : (¬ p2383) ∨ p3156 ∨ (¬ p2284) ∨ (¬ p4489) ∨ (¬ p4506) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4489 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50482 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79092 (p2284 p3156 p3497 p3737 p4506 p5586 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h42210 : (¬ p2284) ∨ (¬ p3497) ∨ (¬ p3737) ∨ (¬ p4506) ∨ (¬ p5586))
    : (¬ p5586) ∨ p3156 ∨ (¬ p4506) ∨ (¬ p3737) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5586 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42210 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79098 (p2156 p2254 p2284 p2911 p2922 p2950 p3156 p3379 p3497 p3646 p4503 p4506 : Prop)
    (h73436 : p3646 ∨ p2156)
    (h73400 : p3497 ∨ p3156)
    (h62373 : (¬ p2254) ∨ (¬ p2284) ∨ (¬ p2911) ∨ (¬ p2922) ∨ (¬ p2950) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3646) ∨ (¬ p4503) ∨ (¬ p4506))
    : (¬ p4503) ∨ (¬ p2950) ∨ p2156 ∨ (¬ p2922) ∨ (¬ p4506) ∨ (¬ p2911) ∨ (¬ p3379) ∨ (¬ p2284) ∨ (¬ p2254) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4503 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h62373 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u10))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u0))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step79099 (p2254 p2396 p2946 p2952 p3093 p3146 p3156 p3309 p3497 p3692 p3950 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h49063 : (¬ p2254) ∨ (¬ p2396) ∨ (¬ p2952) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950))
    : (¬ p3309) ∨ p3146 ∨ (¬ p3950) ∨ (¬ p3093) ∨ p2946 ∨ p3156 ∨ (¬ p2254) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49063 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step79104 (p2901 p2911 p3156 p3497 p4132 p4647 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h49826 : (¬ p2901) ∨ (¬ p2911) ∨ (¬ p3497) ∨ (¬ p4132) ∨ (¬ p4647))
    : (¬ p2911) ∨ (¬ p2901) ∨ (¬ p4647) ∨ (¬ p4132) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49826 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79108 (p2427 p2563 p2901 p3156 p3497 p4235 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73536 : p4235 ∨ p2427)
    (h69490 : (¬ p2901) ∨ (¬ p3497) ∨ (¬ p2563) ∨ (¬ p4235))
    : (¬ p2901) ∨ p3156 ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69490 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79109 (p2220 p2284 p2737 p2811 p2958 p3156 p3497 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h44260 : (¬ p2220) ∨ (¬ p2284) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p3497))
    : p3156 ∨ (¬ p2220) ∨ (¬ p2737) ∨ (¬ p2811) ∨ (¬ p2958) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2737 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h44260 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step79114 (p2166 p2284 p2696 p2742 p3156 p3497 p4365 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h57421 : (¬ p2166) ∨ (¬ p2284) ∨ (¬ p2696) ∨ (¬ p2742) ∨ (¬ p3497) ∨ (¬ p4365))
    : p3156 ∨ (¬ p4365) ∨ (¬ p2742) ∨ (¬ p2696) ∨ (¬ p2166) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p4365 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h57421 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u1)))))))))))))

theorem step79115 (p2619 p2946 p2952 p3156 p3497 p4313 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h71410 : (¬ p2619) ∨ (¬ p3497) ∨ (¬ p2952) ∨ (¬ p4313))
    : (¬ p2619) ∨ p2946 ∨ (¬ p4313) ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4313 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71410 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step79117 (p2254 p2417 p2922 p2946 p2952 p3146 p3156 p3379 p3497 p3692 p3950 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h59524 : (¬ p2254) ∨ (¬ p2417) ∨ (¬ p2922) ∨ (¬ p2952) ∨ (¬ p3379) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950))
    : p3146 ∨ (¬ p2417) ∨ (¬ p3379) ∨ (¬ p2254) ∨ (¬ p2922) ∨ p2946 ∨ p3156 ∨ (¬ p3950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2922 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h59524 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step79118 (p2249 p2417 p2656 p2727 p2946 p2952 p3146 p3156 p3389 p3497 p3692 p3950 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h73448 : p3692 ∨ p3146)
    (h51866 : (¬ p2249) ∨ (¬ p2417) ∨ (¬ p2656) ∨ (¬ p2727) ∨ (¬ p2952) ∨ (¬ p3389) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950))
    : p3156 ∨ (¬ p3389) ∨ (¬ p2417) ∨ (¬ p2249) ∨ p2946 ∨ (¬ p2656) ∨ (¬ p3950) ∨ (¬ p2727) ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2727 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51866 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step79120 (p2252 p2598 p2750 p2753 p2946 p2952 p3146 p3156 p3422 p3497 p3564 p3692 p4330 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h64859 : (¬ p2252) ∨ (¬ p2598) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2952) ∨ (¬ p3422) ∨ (¬ p3497) ∨ (¬ p3564) ∨ (¬ p3692) ∨ (¬ p4330))
    : (¬ p2753) ∨ p3146 ∨ (¬ p3564) ∨ (¬ p3422) ∨ (¬ p2252) ∨ (¬ p2750) ∨ (¬ p4330) ∨ p3156 ∨ (¬ p2598) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2753 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h64859 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step79121 (p2946 p2952 p3146 p3156 p3276 p3355 p3362 p3461 p3497 p3692 p4191 p4330 p4789 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73400 : p3497 ∨ p3156)
    (h73330 : p2952 ∨ p2946)
    (h73448 : p3692 ∨ p3146)
    (h64966 : (¬ p2952) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3362) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4191) ∨ (¬ p4330) ∨ (¬ p4789))
    : p3461 ∨ (¬ p3276) ∨ p3156 ∨ (¬ p3362) ∨ (¬ p4330) ∨ (¬ p4789) ∨ (¬ p3355) ∨ p2946 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4789 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64966 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u12))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u4))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step79124 (p2946 p2952 p3146 p3156 p3266 p3497 p3692 p4444 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73580 : p4444 ∨ p3266)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h45256 : (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4444))
    : p3146 ∨ p3266 ∨ p2946 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45256 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79125 (p3125 p3156 p3323 p3497 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73400 : p3497 ∨ p3156)
    (h69773 : (¬ p3744) ∨ (¬ p3323) ∨ (¬ p3497))
    : (¬ p3323) ∨ p3125 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h69773 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step79127 (p2220 p2255 p2958 p2992 p3156 p3497 p3662 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73440 : p3662 ∨ p2992)
    (h59642 : (¬ p2220) ∨ (¬ p2255) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p3662))
    : p3156 ∨ p2992 ∨ (¬ p2255) ∨ (¬ p2220) ∨ (¬ p2958) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3662 := (Or.elim h73440 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59642 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79129 (p2139 p2220 p2417 p2598 p3055 p3115 p3156 p3201 p3497 p3876 p4278 p4395 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h73486 : p3876 ∨ p3201)
    (h61841 : (¬ p2139) ∨ (¬ p2220) ∨ (¬ p3055) ∨ (¬ p3115) ∨ (¬ p3497) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4395))
    : (¬ p3115) ∨ p3156 ∨ (¬ p2220) ∨ p2417 ∨ p2598 ∨ (¬ p4395) ∨ (¬ p2139) ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4395 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h61841 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step79131 (p2220 p2651 p2657 p2958 p3156 p3497 p4704 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73400 : p3497 ∨ p3156)
    (h73046 : p4704)
    (h41731 : (¬ p2220) ∨ (¬ p2657) ∨ (¬ p2958) ∨ (¬ p3497) ∨ (¬ p4704))
    : (¬ p2958) ∨ p2651 ∨ p3156 ∨ (¬ p2220) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2958 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2651) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4704 := h73046;
    (Or.elim h41731 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79133 (p2122 p2252 p2396 p2750 p2753 p2774 p2946 p2952 p3146 p3156 p3497 p3692 p3950 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h73448 : p3692 ∨ p3146)
    (h64857 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2753) ∨ (¬ p2774) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950))
    : (¬ p2396) ∨ (¬ p2122) ∨ (¬ p2750) ∨ p2946 ∨ (¬ p2252) ∨ p3156 ∨ (¬ p3950) ∨ p3146 ∨ (¬ p2753) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h64857 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step79134 (p2122 p2252 p2396 p2750 p2829 p2946 p2952 p3146 p3156 p3497 p3692 p3950 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73330 : p2952 ∨ p2946)
    (h73400 : p3497 ∨ p3156)
    (h57322 : (¬ p2122) ∨ (¬ p2252) ∨ (¬ p2396) ∨ (¬ p2750) ∨ (¬ p2829) ∨ (¬ p2952) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p3950))
    : (¬ p3950) ∨ p3146 ∨ (¬ p2252) ∨ (¬ p2122) ∨ p2946 ∨ (¬ p2750) ∨ p3156 ∨ (¬ p2829) ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3950 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57322 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u0)))))))))))))))))))

theorem step79137 (p2427 p2459 p3146 p3156 p3497 p3692 p4241 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73400 : p3497 ∨ p3156)
    (h46173 : (¬ p2427) ∨ (¬ p2459) ∨ (¬ p3497) ∨ (¬ p3692) ∨ (¬ p4241))
    : p3146 ∨ p3156 ∨ (¬ p4241) ∨ (¬ p2427) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46173 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79139 (p2373 p2850 p3156 p3497 p4700 p4753 : Prop)
    (h73400 : p3497 ∨ p3156)
    (h42438 : (¬ p2373) ∨ (¬ p2850) ∨ (¬ p3497) ∨ (¬ p4700) ∨ (¬ p4753))
    : (¬ p4700) ∨ p3156 ∨ (¬ p2850) ∨ (¬ p2373) ∨ (¬ p4753) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4700 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3497 := (Or.elim h73400 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42438 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79142 (p2373 p4355 p5840 : Prop)
    (h74131 : (¬ p2373) ∨ (¬ p5840))
    (h12036 : p4355 ∨ p5840)
    : p4355 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4355) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5840) := (Or.elim h74131 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12036 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step79143 (p2187 p2284 p2331 p2563 p2651 p2963 p3989 p4562 p4702 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73638 : p4562 ∨ p2284)
    (h73502 : p3989 ∨ p2187)
    (h67099 : (¬ p4562) ∨ (¬ p2963) ∨ (¬ p2563) ∨ (¬ p3989) ∨ (¬ p2651) ∨ (¬ p4702))
    : p2331 ∨ p2284 ∨ (¬ p4702) ∨ p2187 ∨ (¬ p2563) ∨ (¬ p2651) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4562 := (Or.elim h73638 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67099 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79151 (p2187 p2331 p2946 p2963 p3136 p3745 p3989 p4315 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h73502 : p3989 ∨ p2187)
    (h73550 : p4315 ∨ p3136)
    (h44992 : (¬ p2946) ∨ (¬ p2963) ∨ (¬ p3745) ∨ (¬ p3989) ∨ (¬ p4315))
    : p2331 ∨ (¬ p2946) ∨ p2187 ∨ p3136 ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44992 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u7)))))))))))

theorem step79154 (p2352 p2363 p3256 p3956 p4341 p4347 p4976 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73500 : p3956 ∨ p2352)
    (h49461 : (¬ p3256) ∨ (¬ p3956) ∨ (¬ p4341) ∨ (¬ p4347) ∨ (¬ p4976))
    : (¬ p3256) ∨ (¬ p4341) ∨ p2363 ∨ p2352 ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49461 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79157 (p3156 p5061 p5062 : Prop)
    (h73900 : p5061 ∨ p3156)
    (h8491 : (¬ p5061) ∨ p5062)
    : p3156 ∨ p5062 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5062) := (fun h => hn (Or.inr h));
    let u2 : p5061 := (Or.elim h73900 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8491 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79158 (p3156 p5061 p5063 : Prop)
    (h73900 : p5061 ∨ p3156)
    (h8492 : (¬ p5061) ∨ p5063)
    : p3156 ∨ p5063 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5063) := (fun h => hn (Or.inr h));
    let u2 : p5061 := (Or.elim h73900 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8492 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79159 (p2284 p2563 p3952 p4110 p4241 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73515 : (¬ p2563) ∨ (¬ p4110))
    (h6465 : (¬ p3952) ∨ p4110 ∨ (¬ p4241))
    : (¬ p4241) ∨ p2284 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p4110) := (Or.elim h73515 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6465 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step79163 (p2284 p2563 p3952 p4241 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h27267 : (¬ p2563) ∨ (¬ p3952) ∨ (¬ p4241))
    : (¬ p4241) ∨ p2284 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h27267 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step79165 (p2459 p2563 p2901 p3146 p3692 p4119 p4241 p4320 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h73552 : p4320 ∨ p2901)
    (h53338 : (¬ p2459) ∨ (¬ p2563) ∨ (¬ p3692) ∨ (¬ p4119) ∨ (¬ p4241) ∨ (¬ p4320))
    : p3146 ∨ (¬ p4241) ∨ (¬ p2459) ∨ (¬ p2563) ∨ (¬ p4119) ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4119 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2901) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53338 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step79166 (p2470 p2476 p2630 p2662 p2810 p3136 p4241 p4608 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73316 : p2810 ∨ p2630)
    (h41367 : (¬ p2476) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4608))
    : p2470 ∨ (¬ p4241) ∨ (¬ p2662) ∨ (¬ p4608) ∨ (¬ p3136) ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h41367 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79167 (p2230 p2589 p2655 p2946 p4241 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h20291 : (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4241))
    : (¬ p2655) ∨ (¬ p2946) ∨ (¬ p4241) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2655 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h20291 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step79168 (p2573 p2579 p2630 p2662 p2810 p3136 p4241 p4715 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73316 : p2810 ∨ p2630)
    (h54221 : (¬ p2579) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p3136) ∨ (¬ p4241) ∨ (¬ p4715))
    : (¬ p3136) ∨ (¬ p2662) ∨ (¬ p4715) ∨ p2573 ∨ p2630 ∨ (¬ p4241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54221 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79169 (p2449 p2573 p2579 p3516 p3947 p4241 p4386 p4715 p5201 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73274 : p2579 ∨ p2573)
    (h57716 : (¬ p2579) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4241) ∨ (¬ p4386) ∨ (¬ p4715) ∨ (¬ p5201))
    : (¬ p3516) ∨ p2449 ∨ p2573 ∨ (¬ p4386) ∨ (¬ p5201) ∨ (¬ p4241) ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5201 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57716 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step79172 (p2284 p4336 p5822 : Prop)
    (h74107 : (¬ p2284) ∨ (¬ p5822))
    (h11929 : p4336 ∨ p5822)
    : p4336 ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4336) := (fun h => hn (Or.inl h));
    let u1 : p2284 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5822) := (Or.elim h74107 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11929 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step79173 (p2295 p2363 p2459 p2668 p3568 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73416 : p3568 ∨ p2295)
    (h43461 : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p4348))
    : (¬ p2668) ∨ p2459 ∨ (¬ p2363) ∨ p2295 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43461 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79175 (p2331 p2352 p2651 p2657 p2668 p3956 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73500 : p3956 ∨ p2352)
    (h43187 : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3956))
    : (¬ p2331) ∨ (¬ p2668) ∨ p2651 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43187 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79176 (p2187 p2274 p2641 p2668 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h45721 : (¬ p2274) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2641) ∨ (¬ p2668) ∨ p2187 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45721 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79177 (p2331 p2363 p2651 p2657 p2668 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h56486 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2657) ∨ (¬ p2668))
    : (¬ p2668) ∨ (¬ p2363) ∨ p2651 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h56486 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79178 (p2363 p2641 p2668 p2727 p4111 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h64593 : (¬ p2363) ∨ (¬ p2641) ∨ (¬ p2668) ∨ (¬ p4111))
    : (¬ p2641) ∨ (¬ p2668) ∨ p2727 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h64593 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79180 (p2363 p2668 p3323 p4037 p4604 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h53146 : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4604))
    : p3323 ∨ (¬ p2668) ∨ (¬ p2363) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53146 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step79182 (p2331 p2363 p2459 p2668 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h45488 : (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p4348))
    : (¬ p2331) ∨ (¬ p2668) ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45488 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79185 (p2210 p2668 p2696 p2797 p2881 p2891 p3486 p3555 p3570 p4133 p4733 : Prop)
    (h73412 : p3555 ∨ p2210)
    (h73398 : p3486 ∨ p2891)
    (h73418 : p3570 ∨ p2881)
    (h50538 : (¬ p2668) ∨ (¬ p2696) ∨ (¬ p2797) ∨ (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4133) ∨ (¬ p4733))
    : p2210 ∨ p2891 ∨ (¬ p2797) ∨ (¬ p4733) ∨ p2881 ∨ (¬ p2696) ∨ (¬ p2668) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50538 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u3)))))))))))))))))

theorem step79187 (p2363 p2668 p2737 p2743 p2829 p4328 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h45523 : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2743) ∨ (¬ p2829) ∨ (¬ p4328))
    : (¬ p2829) ∨ (¬ p2668) ∨ (¬ p2363) ∨ p2737 ∨ (¬ p4328) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4328 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45523 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79188 (p2187 p2274 p2331 p2668 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h43283 : (¬ p2274) ∨ (¬ p2331) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2668) ∨ (¬ p2274) ∨ p2187 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43283 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79193 (p2187 p2331 p2651 p2657 p2668 p3989 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73502 : p3989 ∨ p2187)
    (h53894 : (¬ p2331) ∨ (¬ p2657) ∨ (¬ p2668) ∨ (¬ p3989))
    : (¬ p2331) ∨ (¬ p2668) ∨ p2651 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53894 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79195 (p2187 p2630 p2668 p2797 p2810 p3989 : Prop)
    (h73316 : p2810 ∨ p2630)
    (h73502 : p3989 ∨ p2187)
    (h47205 : (¬ p2668) ∨ (¬ p2797) ∨ (¬ p2810) ∨ (¬ p3989))
    : (¬ p2797) ∨ (¬ p2668) ∨ p2630 ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47205 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79197 (p2363 p2668 p3146 p3692 p3988 p4560 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h72955 : p4560)
    (h51558 : (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4560))
    : (¬ p2668) ∨ p3146 ∨ (¬ p3988) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4560 := h72955;
    (Or.elim h51558 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79202 (p2352 p2668 p3019 p3422 p3584 p3956 p4750 : Prop)
    (h73426 : p3584 ∨ p3422)
    (h73500 : p3956 ∨ p2352)
    (h51003 : (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3584) ∨ (¬ p3956) ∨ (¬ p4750))
    : (¬ p2668) ∨ p3422 ∨ (¬ p3019) ∨ (¬ p4750) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51003 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79203 (p2295 p2352 p2573 p2579 p2668 p3568 p3956 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73500 : p3956 ∨ p2352)
    (h73274 : p2579 ∨ p2573)
    (h45971 : (¬ p2579) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3956))
    : (¬ p2668) ∨ p2295 ∨ p2352 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45971 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79204 (p2295 p2352 p2493 p2499 p2668 p3568 p3956 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73500 : p3956 ∨ p2352)
    (h73260 : p2499 ∨ p2493)
    (h43445 : (¬ p2499) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3956))
    : (¬ p2668) ∨ p2295 ∨ p2352 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43445 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79209 (p2352 p2668 p3956 p4389 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h37130 : (¬ p2668) ∨ (¬ p3956) ∨ (¬ p4389))
    : (¬ p2668) ∨ (¬ p4389) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h37130 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79210 (p2363 p2528 p2534 p2668 p3573 p4976 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h42052 : (¬ p2363) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3573) ∨ (¬ p4976))
    : (¬ p2668) ∨ p2528 ∨ (¬ p4976) ∨ (¬ p2363) ∨ (¬ p3573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42052 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79212 (p2470 p2476 p2573 p2668 p4432 p4976 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h59651 : (¬ p2476) ∨ (¬ p2573) ∨ (¬ p2668) ∨ (¬ p4432) ∨ (¬ p4976))
    : p2470 ∨ (¬ p2668) ∨ (¬ p2573) ∨ (¬ p4976) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59651 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79213 (p2246 p2331 p2363 p2608 p2668 p2744 p3399 p3631 p3817 p4366 p4669 : Prop)
    (h73570 : p4366 ∨ p3399)
    (h73468 : p3817 ∨ p3631)
    (h58006 : (¬ p2246) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2608) ∨ (¬ p2668) ∨ (¬ p2744) ∨ (¬ p3817) ∨ (¬ p4366) ∨ (¬ p4669))
    : p3399 ∨ (¬ p2668) ∨ (¬ p2608) ∨ (¬ p2246) ∨ (¬ p2744) ∨ (¬ p4669) ∨ (¬ p2363) ∨ p3631 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3631) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4366 := (Or.elim h73570 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3817 := (Or.elim h73468 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h58006 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step79216 (p2295 p2668 p2881 p3550 p3568 p3570 p4556 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73418 : p3570 ∨ p2881)
    (h50560 : (¬ p2668) ∨ (¬ p3550) ∨ (¬ p3568) ∨ (¬ p3570) ∨ (¬ p4556))
    : (¬ p2668) ∨ p2295 ∨ (¬ p3550) ∨ p2881 ∨ (¬ p4556) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2295) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79218 (p2352 p2493 p2499 p2668 p2922 p3956 : Prop)
    (h73500 : p3956 ∨ p2352)
    (h73260 : p2499 ∨ p2493)
    (h63465 : (¬ p2499) ∨ (¬ p2668) ∨ (¬ p2922) ∨ (¬ p3956))
    : (¬ p2922) ∨ (¬ p2668) ∨ p2352 ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63465 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79222 (p2132 p2138 p2331 p2363 p2668 p2870 p3246 p3690 p4244 p4669 p4786 : Prop)
    (h73214 : p2138 ∨ p2132)
    (h73540 : p4244 ∨ p2870)
    (h73446 : p3690 ∨ p3246)
    (h54399 : (¬ p2138) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3690) ∨ (¬ p4244) ∨ (¬ p4669) ∨ (¬ p4786))
    : (¬ p2668) ∨ (¬ p2363) ∨ (¬ p2331) ∨ p2132 ∨ p2870 ∨ (¬ p4786) ∨ (¬ p4669) ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2132) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3246) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2138 := (Or.elim h73214 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54399 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step79223 (p2274 p2295 p2352 p2668 p3568 p3956 p3958 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73500 : p3956 ∨ p2352)
    (h51967 : (¬ p2274) ∨ (¬ p2668) ∨ (¬ p3568) ∨ (¬ p3956) ∨ (¬ p3958))
    : p2295 ∨ (¬ p2668) ∨ (¬ p3958) ∨ p2352 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51967 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79225 (p2383 p2387 p2667 p2668 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h3461 : (¬ p2387) ∨ (¬ p2667) ∨ (¬ p2668))
    : (¬ p2668) ∨ p2383 ∨ (¬ p2667) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h3461 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step79226 (p2230 p2248 p2331 p2363 p2589 p2668 p2870 p2982 p3105 p4108 p4244 p4948 : Prop)
    (h73540 : p4244 ∨ p2870)
    (h73284 : p2589 ∨ p2230)
    (h73846 : p4948 ∨ p2982)
    (h49130 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2589) ∨ (¬ p2668) ∨ (¬ p3105) ∨ (¬ p4108) ∨ (¬ p4244) ∨ (¬ p4948))
    : (¬ p3105) ∨ (¬ p2668) ∨ (¬ p4108) ∨ p2870 ∨ (¬ p2248) ∨ (¬ p2331) ∨ p2230 ∨ p2982 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4108 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2870) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4244 := (Or.elim h73540 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u11 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h49130 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u11)))))))))))))))))))

theorem step79227 (p2352 p2440 p2573 p2579 p2668 p3019 p3956 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h45863 : (¬ p2440) ∨ (¬ p2579) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3956))
    : (¬ p2668) ∨ p2573 ∨ (¬ p2440) ∨ (¬ p3019) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45863 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79228 (p2352 p2440 p2493 p2499 p2668 p3019 p3956 p4257 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h55488 : (¬ p2440) ∨ (¬ p2499) ∨ (¬ p2668) ∨ (¬ p3019) ∨ (¬ p3956) ∨ (¬ p4257))
    : (¬ p2668) ∨ (¬ p2440) ∨ (¬ p3019) ∨ p2493 ∨ (¬ p4257) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4257 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h55488 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step79230 (p2528 p2668 p3323 p4037 p4171 p4384 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h59372 : (¬ p2528) ∨ (¬ p2668) ∨ (¬ p4037) ∨ (¬ p4171) ∨ (¬ p4384))
    : p3323 ∨ (¬ p4171) ∨ (¬ p2528) ∨ (¬ p4384) ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59372 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79234 (p2383 p2387 p2668 p3266 p5274 p5284 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h46944 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p3266) ∨ (¬ p5274) ∨ (¬ p5284))
    : (¬ p5274) ∨ (¬ p5284) ∨ (¬ p3266) ∨ p2383 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46944 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step79235 (p2274 p2295 p2363 p2668 p3568 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h53623 : (¬ p2274) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3568))
    : p2295 ∨ (¬ p2668) ∨ (¬ p2363) ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h53623 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79236 (p2383 p2387 p2563 p2668 p4110 p4336 p4356 p4705 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h73516 : p4110 ∨ p2563)
    (h42053 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2668) ∨ (¬ p4336) ∨ p2383 ∨ (¬ p4705) ∨ p2563 ∨ (¬ p4356) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42053 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79238 (p2553 p2588 p2668 p3323 p3564 p4037 p4405 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73282 : p2588 ∨ p2553)
    (h48135 : (¬ p2588) ∨ (¬ p2668) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4405))
    : p3323 ∨ (¬ p3564) ∨ (¬ p4405) ∨ (¬ p2668) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48135 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79243 (p2668 p3323 p3979 p4037 p4171 p5568 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h59756 : (¬ p2668) ∨ (¬ p3979) ∨ (¬ p4037) ∨ (¬ p4171) ∨ (¬ p5568))
    : (¬ p5568) ∨ (¬ p2668) ∨ (¬ p3979) ∨ (¬ p4171) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59756 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79246 (p2295 p2383 p2387 p2668 p2737 p2743 p3361 p3568 p3983 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73298 : p2743 ∨ p2737)
    (h73246 : p2387 ∨ p2383)
    (h46868 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2743) ∨ (¬ p3361) ∨ (¬ p3568) ∨ (¬ p3983))
    : (¬ p3983) ∨ (¬ p2668) ∨ p2295 ∨ (¬ p3361) ∨ p2737 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u8 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46868 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step79249 (p2383 p2387 p2668 p2797 p3983 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h71415 : (¬ p2387) ∨ (¬ p2797) ∨ (¬ p2668) ∨ (¬ p3983))
    : (¬ p2668) ∨ (¬ p3983) ∨ (¬ p2797) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71415 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step79251 (p2383 p2387 p2598 p2668 p2785 p3055 p3323 p3425 p3434 p3471 p4037 p4625 p4749 p4841 : Prop)
    (h73350 : p3055 ∨ p2598)
    (h73508 : p4037 ∨ p3323)
    (h73246 : p2387 ∨ p2383)
    (h73396 : p3471 ∨ p3425)
    (h63346 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2785) ∨ (¬ p3055) ∨ (¬ p3434) ∨ (¬ p3471) ∨ (¬ p4037) ∨ (¬ p4625) ∨ (¬ p4749) ∨ (¬ p4841))
    : (¬ p2785) ∨ (¬ p2668) ∨ p2598 ∨ (¬ p4749) ∨ p3323 ∨ p2383 ∨ (¬ p4841) ∨ (¬ p3434) ∨ p3425 ∨ (¬ p4625) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2785 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4841 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3425) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4625 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u13 : p3471 := (Or.elim h73396 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63346 (fun q0 => (False.elim (q0 u12))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u3))) (fun r8 => (False.elim (r8 u6)))))))))))))))))))))

theorem step79254 (p2248 p2331 p2459 p2509 p2668 p3379 p3452 p3550 p4149 p4286 p5118 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73394 : p3452 ∨ p3379)
    (h50433 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2459) ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p3550) ∨ (¬ p4286) ∨ (¬ p5118))
    : p4149 ∨ (¬ p2509) ∨ (¬ p2668) ∨ (¬ p2459) ∨ (¬ p3550) ∨ p3379 ∨ (¬ p2331) ∨ (¬ p5118) ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50433 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u4))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step79255 (p2331 p2668 p2946 p2952 p3136 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h62056 : (¬ p2331) ∨ (¬ p2668) ∨ (¬ p2952) ∨ (¬ p3136))
    : (¬ p2668) ∨ (¬ p2331) ∨ (¬ p3136) ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62056 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step79259 (p2427 p2563 p2668 p3745 p4235 p4275 p4405 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h54706 : (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3745) ∨ (¬ p4235) ∨ (¬ p4275) ∨ (¬ p4405))
    : (¬ p2668) ∨ p2427 ∨ (¬ p2563) ∨ (¬ p4275) ∨ (¬ p4405) ∨ (¬ p3745) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54706 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step79263 (p2563 p2668 p3125 p3323 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h44506 : (¬ p2563) ∨ (¬ p2668) ∨ (¬ p3125) ∨ (¬ p4037))
    : (¬ p3125) ∨ p3323 ∨ (¬ p2668) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h44506 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79266 (p2295 p2383 p2387 p2668 p2787 p3362 p3389 p3568 p3868 p4556 p5660 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73246 : p2387 ∨ p2383)
    (h64699 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p3868) ∨ (¬ p4556) ∨ (¬ p5660))
    : (¬ p3868) ∨ (¬ p5660) ∨ (¬ p2668) ∨ (¬ p3389) ∨ p2295 ∨ (¬ p2787) ∨ (¬ p3362) ∨ (¬ p4556) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3868 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5660 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4556 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h64699 (fun q0 => (False.elim (q0 u10))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u0))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u7))) (fun r7 => (False.elim (r7 u1)))))))))))))))))))

theorem step79270 (p2295 p4361 p4571 : Prop)
    (h73644 : p4571 ∨ (¬ p2295))
    (h7245 : p4361 ∨ (¬ p4571))
    : p4361 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4361) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4571 := (Or.elim h73644 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7245 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step79271 (p2295 p2331 p2553 p2588 p3564 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h43704 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p3564))
    : (¬ p2295) ∨ p2553 ∨ (¬ p3564) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43704 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step79272 (p2295 p2352 p3323 p3564 p3956 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73500 : p3956 ∨ p2352)
    (h44212 : (¬ p2295) ∨ (¬ p3564) ∨ (¬ p3956) ∨ (¬ p4037))
    : (¬ p2295) ∨ p3323 ∨ p2352 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44212 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79273 (p2274 p2295 p3097 p3323 p3564 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73352 : p3097 ∨ p2274)
    (h60748 : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3564) ∨ (¬ p4037))
    : (¬ p2295) ∨ p3323 ∨ p2274 ∨ (¬ p3564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60748 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79276 (p2295 p2307 p2313 p2386 p3019 p3422 p3584 p4750 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73426 : p3584 ∨ p3422)
    (h57742 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p3019) ∨ (¬ p3584) ∨ (¬ p4750))
    : p2307 ∨ (¬ p2295) ∨ p3422 ∨ (¬ p4750) ∨ (¬ p3019) ∨ (¬ p2386) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4750 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57742 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79278 (p2295 p2553 p2573 p2579 p2588 p2659 p3019 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h41816 : (¬ p2295) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2659) ∨ (¬ p3019))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2659) ∨ p2573 ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2659 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41816 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79279 (p2295 p2774 p3323 p3483 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h43048 : (¬ p2295) ∨ (¬ p2774) ∨ (¬ p3483) ∨ (¬ p4037))
    : (¬ p3483) ∨ p3323 ∨ (¬ p2295) ∨ (¬ p2774) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3483 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43048 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79281 (p2295 p2573 p3389 p3540 p3921 p4976 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h41690 : (¬ p2295) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4976))
    : (¬ p2295) ∨ (¬ p3921) ∨ p3389 ∨ (¬ p4976) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41690 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79282 (p2295 p2352 p2363 p2553 p2588 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h46697 : (¬ p2295) ∨ (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2588))
    : (¬ p2295) ∨ (¬ p2352) ∨ (¬ p2363) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46697 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79283 (p2295 p2553 p2588 p4389 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h20173 : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p4389))
    : (¬ p2295) ∨ (¬ p4389) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20173 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79284 (p2241 p2295 p2553 p2588 p2641 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h43165 : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2641))
    : (¬ p2641) ∨ (¬ p2295) ∨ p2553 ∨ (¬ p2241) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43165 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79286 (p2295 p2553 p2588 p2641 p2727 p4111 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73518 : p4111 ∨ p2727)
    (h62330 : (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2641) ∨ (¬ p4111))
    : (¬ p2295) ∨ (¬ p2641) ∨ p2553 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62330 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79287 (p2295 p2331 p2553 p2588 p2651 p2657 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73288 : p2657 ∨ p2651)
    (h42774 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2588) ∨ (¬ p2657))
    : (¬ p2295) ∨ p2553 ∨ p2651 ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42774 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79289 (p2241 p2274 p2295 p2641 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h47666 : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p3097))
    : (¬ p2641) ∨ (¬ p2295) ∨ (¬ p2241) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47666 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79291 (p2274 p2295 p2331 p2651 p2657 p3097 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h73352 : p3097 ∨ p2274)
    (h57710 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2657) ∨ (¬ p3097))
    : (¬ p2295) ∨ (¬ p2331) ∨ p2651 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57710 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79292 (p2274 p2295 p2331 p2946 p2952 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73330 : p2952 ∨ p2946)
    (h44385 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3097))
    : (¬ p2295) ∨ (¬ p2331) ∨ p2274 ∨ p2946 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44385 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79294 (p2295 p2307 p2313 p2577 p2655 p2797 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h71416 : (¬ p2797) ∨ (¬ p2313) ∨ (¬ p2577) ∨ (¬ p2655) ∨ (¬ p2295))
    : (¬ p2295) ∨ (¬ p2655) ∨ (¬ p2797) ∨ p2307 ∨ (¬ p2577) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h71416 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79301 (p2295 p2307 p2313 p2386 p2440 p3019 p4717 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h40921 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2440) ∨ (¬ p3019) ∨ (¬ p4717))
    : p2307 ∨ (¬ p2295) ∨ (¬ p2386) ∨ (¬ p4717) ∨ (¬ p2440) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2386 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h40921 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79304 (p2230 p2295 p2440 p2553 p2588 p2663 p3019 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h63971 : (¬ p2230) ∨ (¬ p2295) ∨ (¬ p2440) ∨ (¬ p2588) ∨ (¬ p2663) ∨ (¬ p3019))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2663) ∨ (¬ p2230) ∨ (¬ p3019) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h63971 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step79307 (p2295 p2307 p2313 p2386 p2493 p2499 p3019 p4811 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73260 : p2499 ∨ p2493)
    (h41151 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2386) ∨ (¬ p2499) ∨ (¬ p3019) ∨ (¬ p4811))
    : (¬ p2386) ∨ (¬ p2295) ∨ p2307 ∨ p2493 ∨ (¬ p4811) ∨ (¬ p3019) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2386 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3019 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41151 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step79312 (p2156 p2295 p3051 p3556 p4275 p4560 : Prop)
    (h73414 : p3556 ∨ p3051)
    (h72955 : p4560)
    (h50943 : (¬ p2156) ∨ (¬ p2295) ∨ (¬ p3556) ∨ (¬ p4275) ∨ (¬ p4560))
    : p3051 ∨ (¬ p2295) ∨ (¬ p4275) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4560 := h72955;
    (Or.elim h50943 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79315 (p2177 p2295 p2881 p3570 p4204 p4560 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h72955 : p4560)
    (h47995 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3570) ∨ (¬ p4204) ∨ (¬ p4560))
    : (¬ p2295) ∨ p2881 ∨ (¬ p2177) ∨ (¬ p4204) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4204 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4560 := h72955;
    (Or.elim h47995 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79319 (p2295 p3246 p3323 p4037 p4396 p4559 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h58428 : (¬ p2295) ∨ (¬ p3246) ∨ (¬ p4037) ∨ (¬ p4396) ∨ (¬ p4559))
    : (¬ p3246) ∨ p3323 ∨ (¬ p4396) ∨ (¬ p4559) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h58428 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79320 (p2295 p2321 p3323 p3516 p4037 p4396 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h48393 : (¬ p2295) ∨ (¬ p2321) ∨ (¬ p3516) ∨ (¬ p4037) ∨ (¬ p4396))
    : (¬ p3516) ∨ (¬ p2321) ∨ p3323 ∨ (¬ p4396) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2321 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48393 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79322 (p2295 p2417 p3323 p4037 p4396 p4712 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h56370 : (¬ p2295) ∨ (¬ p2417) ∨ (¬ p4037) ∨ (¬ p4396) ∨ (¬ p4712))
    : (¬ p2295) ∨ (¬ p2417) ∨ (¬ p4396) ∨ (¬ p4712) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56370 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79325 (p2295 p2396 p2668 p3324 p4138 p4668 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h55447 : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4668))
    : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p4668) ∨ p2668 ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h55447 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79331 (p2088 p2295 p3256 p4118 p4170 p4196 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h71418 : (¬ p4118) ∨ (¬ p4170) ∨ (¬ p4196) ∨ (¬ p2295) ∨ (¬ p2088))
    : p3256 ∨ (¬ p2295) ∨ (¬ p4196) ∨ (¬ p4170) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4196 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71418 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79335 (p2295 p2331 p3166 p3172 p4432 p4437 : Prop)
    (h73356 : p3172 ∨ p3166)
    (h71420 : (¬ p4432) ∨ (¬ p3172) ∨ (¬ p2295) ∨ (¬ p4437) ∨ (¬ p2331))
    : p3166 ∨ (¬ p2295) ∨ (¬ p4437) ∨ (¬ p2331) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3166) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3172 := (Or.elim h73356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71420 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79343 (p2295 p2668 p3093 p3309 p3324 p3549 p3591 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73406 : p3549 ∨ p3309)
    (h73386 : p3324 ∨ p2668)
    (h46193 : (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3549) ∨ (¬ p3591))
    : p3093 ∨ (¬ p2295) ∨ p3309 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46193 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79344 (p2295 p2312 p2341 p2668 p3324 p4503 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h41437 : (¬ p2295) ∨ (¬ p2312) ∨ (¬ p2341) ∨ (¬ p3324) ∨ (¬ p4503))
    : (¬ p2295) ∨ (¬ p2341) ∨ p2668 ∨ (¬ p2312) ∨ (¬ p4503) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41437 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79349 (p2295 p2307 p2313 p2668 p2737 p2743 p3324 p3361 p3983 : Prop)
    (h73298 : p2743 ∨ p2737)
    (h73238 : p2313 ∨ p2307)
    (h73386 : p3324 ∨ p2668)
    (h46813 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2743) ∨ (¬ p3324) ∨ (¬ p3361) ∨ (¬ p3983))
    : (¬ p3983) ∨ (¬ p2295) ∨ p2737 ∨ p2307 ∨ (¬ p3361) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3983 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2737) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3361 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2743 := (Or.elim h73298 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46813 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step79350 (p2295 p2668 p3324 p3791 p4138 p5564 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h41665 : (¬ p2295) ∨ (¬ p3324) ∨ (¬ p3791) ∨ (¬ p4138) ∨ (¬ p5564))
    : (¬ p3791) ∨ (¬ p5564) ∨ (¬ p4138) ∨ p2668 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3791 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41665 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step79352 (p2295 p3323 p3325 p3990 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h20637 : (¬ p2295) ∨ (¬ p3325) ∨ (¬ p3990) ∨ (¬ p4037))
    : (¬ p2295) ∨ (¬ p3325) ∨ (¬ p3990) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h20637 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79355 (p2187 p2230 p2241 p2295 p2563 p2589 p2641 p3989 p4110 p5193 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h73502 : p3989 ∨ p2187)
    (h71421 : (¬ p3989) ∨ (¬ p2241) ∨ (¬ p5193) ∨ (¬ p2295) ∨ (¬ p4110) ∨ (¬ p2641) ∨ (¬ p2589))
    : (¬ p2641) ∨ (¬ p2295) ∨ p2563 ∨ p2230 ∨ (¬ p2241) ∨ (¬ p5193) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u9 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71421 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (False.elim (r5 u8)))))))))))))))

theorem step79356 (p2295 p2341 p2641 p2696 p2742 p2911 p3363 p3367 p3551 p3585 p4712 p5197 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73428 : p3585 ∨ p3367)
    (h71422 : (¬ p2641) ∨ (¬ p3585) ∨ (¬ p3363) ∨ (¬ p3551) ∨ (¬ p5197) ∨ (¬ p2295) ∨ (¬ p2696) ∨ (¬ p2911) ∨ (¬ p2742) ∨ (¬ p4712))
    : (¬ p2911) ∨ (¬ p2295) ∨ p2341 ∨ (¬ p2696) ∨ (¬ p5197) ∨ p3367 ∨ (¬ p2641) ∨ (¬ p3363) ∨ (¬ p2742) ∨ (¬ p4712) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5197 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2742 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4712 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h71422 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u11))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u9)))))))))))))))))))))

theorem step79358 (p2177 p2295 p2911 p3581 p3644 p4976 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h41815 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3581) ∨ (¬ p3644) ∨ (¬ p4976))
    : p2911 ∨ (¬ p2295) ∨ (¬ p2177) ∨ (¬ p4976) ∨ (¬ p3581) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41815 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79361 (p2295 p2668 p2881 p3324 p4138 p4559 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h48283 : (¬ p2295) ∨ (¬ p2881) ∨ (¬ p3324) ∨ (¬ p4138) ∨ (¬ p4559))
    : (¬ p2881) ∨ (¬ p2295) ∨ p2668 ∨ (¬ p4559) ∨ (¬ p4138) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48283 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79363 (p2295 p2363 p2459 p2668 p3324 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h52342 : (¬ p2295) ∨ (¬ p2459) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2295) ∨ p2363 ∨ p2668 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52342 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79364 (p2295 p2307 p2313 p2563 p2668 p3324 p4110 p4356 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73386 : p3324 ∨ p2668)
    (h73516 : p4110 ∨ p2563)
    (h56690 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p4110) ∨ (¬ p4356))
    : p2307 ∨ (¬ p2295) ∨ p2668 ∨ (¬ p4356) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56690 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79365 (p2295 p2307 p2313 p2363 p2668 p3324 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h73238 : p2313 ∨ p2307)
    (h42810 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3324) ∨ (¬ p4347))
    : (¬ p2295) ∨ p2363 ∨ p2668 ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42810 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79368 (p2177 p2255 p2295 p2331 p2417 p2662 p2727 p3389 p3540 p4111 p4278 p4666 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73402 : p3540 ∨ p3389)
    (h73518 : p4111 ∨ p2727)
    (h60337 : (¬ p2177) ∨ (¬ p2255) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2662) ∨ (¬ p3540) ∨ (¬ p4111) ∨ (¬ p4278) ∨ (¬ p4666))
    : p2417 ∨ (¬ p2295) ∨ (¬ p2662) ∨ p3389 ∨ p2727 ∨ (¬ p2255) ∨ (¬ p4666) ∨ (¬ p2177) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2255 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60337 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step79370 (p2295 p2331 p2946 p2952 p3136 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h62055 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2952) ∨ (¬ p3136))
    : (¬ p2331) ∨ (¬ p2295) ∨ p2946 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2946) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62055 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step79374 (p2249 p2295 p2307 p2313 p2641 p3983 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h51739 : (¬ p2249) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2641) ∨ (¬ p3983))
    : (¬ p2641) ∨ (¬ p2295) ∨ (¬ p2249) ∨ (¬ p3983) ∨ p2307 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2249 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51739 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79376 (p2274 p2295 p2406 p2493 p2578 p2667 p3097 p3238 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73374 : p3238 ∨ p2406)
    (h47388 : (¬ p2295) ∨ (¬ p2493) ∨ (¬ p2578) ∨ (¬ p2667) ∨ (¬ p3097) ∨ (¬ p3238))
    : (¬ p2295) ∨ p2274 ∨ p2406 ∨ (¬ p2667) ∨ (¬ p2493) ∨ (¬ p2578) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2667 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2578 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47388 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step79378 (p2295 p2307 p2313 p2946 p3983 p4563 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h54164 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2946) ∨ (¬ p3983) ∨ (¬ p4563))
    : p2307 ∨ (¬ p3983) ∨ (¬ p4563) ∨ (¬ p2295) ∨ (¬ p2946) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54164 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79379 (p2295 p2396 p3246 p3690 p4107 p4560 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h72955 : p4560)
    (h73513 : (¬ p2396) ∨ (¬ p4107))
    (h66930 : p4107 ∨ (¬ p3690) ∨ (¬ p2295) ∨ (¬ p4560))
    : (¬ p2295) ∨ p3246 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : p4560 := h72955;
    let u5 : (¬ p4107) := (Or.elim h73513 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h66930 (fun q0 => (False.elim (u5 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79383 (p2295 p2307 p2313 p2797 p3983 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h71425 : (¬ p2797) ∨ (¬ p2313) ∨ (¬ p3983) ∨ (¬ p2295))
    : p2307 ∨ (¬ p3983) ∨ (¬ p2797) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2307) := (fun h => hn (Or.inl h));
    let u1 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71425 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step79386 (p2295 p2307 p2313 p2797 p3654 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h56350 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2797) ∨ (¬ p3654))
    : (¬ p3654) ∨ p2307 ∨ (¬ p2797) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h56350 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79388 (p2295 p2363 p3146 p3325 p3692 p3988 p4560 : Prop)
    (h73448 : p3692 ∨ p3146)
    (h72955 : p4560)
    (h62245 : (¬ p2295) ∨ (¬ p2363) ∨ (¬ p3325) ∨ (¬ p3692) ∨ (¬ p3988) ∨ (¬ p4560))
    : (¬ p2295) ∨ p3146 ∨ (¬ p3325) ∨ (¬ p3988) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3325 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4560 := h72955;
    (Or.elim h62245 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step79389 (p2177 p2295 p2331 p2651 p2657 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h44890 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2657))
    : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2177) ∨ p2651 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44890 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79390 (p2254 p2295 p2307 p2313 p2373 p2406 p2668 p3324 p3379 p3983 p4433 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73386 : p3324 ∨ p2668)
    (h63350 : (¬ p2254) ∨ (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2373) ∨ (¬ p2406) ∨ (¬ p3324) ∨ (¬ p3379) ∨ (¬ p3983) ∨ (¬ p4433))
    : (¬ p2406) ∨ (¬ p2295) ∨ (¬ p2373) ∨ (¬ p3983) ∨ p2307 ∨ (¬ p3379) ∨ (¬ p4433) ∨ (¬ p2254) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2373 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3983 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3379 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h63350 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step79391 (p2241 p2295 p2641 p2881 p2911 p3389 p3540 p3644 p4559 p5193 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73402 : p3540 ∨ p3389)
    (h60472 : (¬ p2241) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2881) ∨ (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4559) ∨ (¬ p5193))
    : (¬ p2641) ∨ (¬ p2241) ∨ p2911 ∨ p3389 ∨ (¬ p2881) ∨ (¬ p2295) ∨ (¬ p5193) ∨ (¬ p4559) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60472 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step79393 (p2295 p2396 p2881 p3516 p3821 p4283 : Prop)
    (h73470 : p3821 ∨ p3516)
    (h57305 : (¬ p2295) ∨ (¬ p2396) ∨ (¬ p2881) ∨ (¬ p3821) ∨ (¬ p4283))
    : (¬ p2295) ∨ (¬ p2396) ∨ p3516 ∨ (¬ p2881) ∨ (¬ p4283) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3516) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4283 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3821 := (Or.elim h73470 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57305 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79396 (p2088 p2177 p2295 p2331 p2957 p3136 p3146 p3697 p3857 p4315 p4790 p4905 : Prop)
    (h73480 : p3857 ∨ p2088)
    (h73550 : p4315 ∨ p3136)
    (h53222 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2957) ∨ (¬ p3146) ∨ (¬ p3697) ∨ (¬ p3857) ∨ (¬ p4315) ∨ (¬ p4790) ∨ (¬ p4905))
    : (¬ p2295) ∨ p2088 ∨ (¬ p3146) ∨ (¬ p2177) ∨ (¬ p4905) ∨ p3136 ∨ (¬ p2957) ∨ (¬ p2331) ∨ (¬ p3697) ∨ (¬ p4790) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2088) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3136) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2957 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p4790 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4315 := (Or.elim h73550 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h53222 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u9))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step79403 (p2295 p2761 p3323 p3461 p4037 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h43756 : (¬ p2295) ∨ (¬ p2761) ∨ (¬ p4037) ∨ (¬ p4191))
    : p3461 ∨ p3323 ∨ (¬ p2761) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43756 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79404 (p2295 p3276 p3323 p3461 p4037 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73508 : p4037 ∨ p3323)
    (h43698 : (¬ p2295) ∨ (¬ p3276) ∨ (¬ p4037) ∨ (¬ p4191))
    : (¬ p3276) ∨ p3461 ∨ p3323 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43698 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79408 (p2156 p2187 p2295 p2668 p2958 p3324 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h42996 : (¬ p2156) ∨ (¬ p2187) ∨ (¬ p2295) ∨ (¬ p2958) ∨ (¬ p3324))
    : p2668 ∨ (¬ p2187) ∨ (¬ p2156) ∨ (¬ p2958) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42996 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79409 (p2187 p2274 p2295 p2946 p3097 p4336 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h47765 : (¬ p2187) ∨ (¬ p2295) ∨ (¬ p2946) ∨ (¬ p3097) ∨ (¬ p4336))
    : (¬ p2295) ∨ p2274 ∨ (¬ p2946) ∨ (¬ p4336) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47765 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79411 (p2295 p2331 p2352 p2553 p2588 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h47640 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2352) ∨ (¬ p2588))
    : (¬ p2295) ∨ p2553 ∨ (¬ p2352) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47640 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79412 (p2295 p2307 p2313 p2860 p3758 p4336 p4356 p4906 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73456 : p3758 ∨ p2860)
    (h41640 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3758) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4906))
    : (¬ p2295) ∨ p2307 ∨ (¬ p4356) ∨ (¬ p4336) ∨ p2860 ∨ (¬ p4906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4906 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41640 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step79413 (p2295 p2307 p2313 p3564 p3654 p4137 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73524 : p4137 ∨ p3564)
    (h47886 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3654) ∨ p2307 ∨ (¬ p2295) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47886 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79414 (p2295 p2307 p2313 p2563 p4110 p4336 p4356 p4705 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h73516 : p4110 ∨ p2563)
    (h57466 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p4110) ∨ (¬ p4336) ∨ (¬ p4356) ∨ (¬ p4705))
    : (¬ p2295) ∨ p2307 ∨ p2563 ∨ (¬ p4705) ∨ (¬ p4356) ∨ (¬ p4336) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2307) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4356 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4336 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h57466 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79417 (p2241 p2247 p2295 p2553 p2588 p2797 p3189 p3564 p3609 p4330 p4340 p4360 p4967 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73282 : p2588 ∨ p2553)
    (h73226 : p2247 ∨ p2241)
    (h73566 : p4360 ∨ p3189)
    (h46311 : (¬ p2247) ∨ (¬ p2295) ∨ (¬ p2588) ∨ (¬ p2797) ∨ (¬ p3564) ∨ (¬ p4330) ∨ (¬ p4340) ∨ (¬ p4360) ∨ (¬ p4967))
    : p3609 ∨ (¬ p3564) ∨ p2553 ∨ (¬ p2797) ∨ p2241 ∨ p3189 ∨ (¬ p4330) ∨ (¬ p4967) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3189) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4967 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h46311 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u12))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step79418 (p2295 p2619 p2668 p2860 p3324 p3758 p4441 : Prop)
    (h73456 : p3758 ∨ p2860)
    (h73386 : p3324 ∨ p2668)
    (h47307 : (¬ p2295) ∨ (¬ p2619) ∨ (¬ p3324) ∨ (¬ p3758) ∨ (¬ p4441))
    : (¬ p2295) ∨ (¬ p2619) ∨ (¬ p4441) ∨ p2860 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2860) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3758 := (Or.elim h73456 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47307 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79419 (p2295 p2331 p2396 p2528 p2534 p2598 p3055 p3641 p3874 p3950 p4786 : Prop)
    (h73484 : p3874 ∨ p3641)
    (h73268 : p2534 ∨ p2528)
    (h73350 : p3055 ∨ p2598)
    (h57332 : (¬ p2295) ∨ (¬ p2331) ∨ (¬ p2396) ∨ (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p3950) ∨ (¬ p4786))
    : p3641 ∨ p2528 ∨ (¬ p2396) ∨ (¬ p3950) ∨ (¬ p4786) ∨ (¬ p2331) ∨ (¬ p2295) ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h57332 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79422 (p2177 p2295 p2331 p2417 p2598 p3055 p3201 p3876 p4278 p4666 p4786 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73546 : p4278 ∨ p2417)
    (h73350 : p3055 ∨ p2598)
    (h52250 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3055) ∨ (¬ p3876) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4786))
    : p3201 ∨ p2417 ∨ (¬ p2177) ∨ (¬ p2331) ∨ (¬ p4786) ∨ p2598 ∨ (¬ p2295) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4786 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h52250 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79426 (p2295 p2493 p2499 p2553 p2588 p3379 p3452 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73282 : p2588 ∨ p2553)
    (h44181 : (¬ p2295) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452))
    : p2493 ∨ (¬ p2295) ∨ p3379 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44181 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79427 (p2252 p2295 p2641 p2946 p2952 p3136 : Prop)
    (h73330 : p2952 ∨ p2946)
    (h61494 : (¬ p2252) ∨ (¬ p2295) ∨ (¬ p2641) ∨ (¬ p2952) ∨ (¬ p3136))
    : (¬ p2641) ∨ p2946 ∨ (¬ p3136) ∨ (¬ p2252) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2946) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3136 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2252 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2952 := (Or.elim h73330 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61494 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79433 (p2274 p2295 p3097 p3319 p3323 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73352 : p3097 ∨ p2274)
    (h44505 : (¬ p2295) ∨ (¬ p3097) ∨ (¬ p3319) ∨ (¬ p4037))
    : (¬ p3319) ∨ p3323 ∨ p2274 ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44505 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79435 (p2295 p3093 p3319 p3323 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h45337 : (¬ p2295) ∨ (¬ p3093) ∨ (¬ p3319) ∨ (¬ p4037))
    : (¬ p3319) ∨ (¬ p2295) ∨ (¬ p3093) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45337 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79439 (p2274 p2295 p2563 p3097 p4110 p4705 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h68872 : (¬ p2295) ∨ (¬ p4705) ∨ (¬ p3097) ∨ (¬ p4110))
    : (¬ p2295) ∨ p2274 ∨ (¬ p4705) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4705 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h68872 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79442 (p2295 p2563 p2982 p3323 p4037 p4110 p5045 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73516 : p4110 ∨ p2563)
    (h44022 : (¬ p2295) ∨ (¬ p2982) ∨ (¬ p4037) ∨ (¬ p4110) ∨ (¬ p5045))
    : p3323 ∨ (¬ p2295) ∨ (¬ p5045) ∨ (¬ p2982) ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2982 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44022 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79443 (p2177 p2295 p3125 p3323 p4037 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h47697 : (¬ p2177) ∨ (¬ p2295) ∨ (¬ p3125) ∨ (¬ p4037))
    : (¬ p2295) ∨ p3323 ∨ (¬ p3125) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47697 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79444 (p2295 p2307 p2313 p2383 p2641 : Prop)
    (h73238 : p2313 ∨ p2307)
    (h43213 : (¬ p2295) ∨ (¬ p2313) ∨ (¬ p2383) ∨ (¬ p2641))
    : (¬ p2295) ∨ (¬ p2641) ∨ p2307 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43213 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step79450 (p2230 p2295 p2383 p2584 p2589 p2668 p3324 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73284 : p2589 ∨ p2230)
    (h43209 : (¬ p2295) ∨ (¬ p2383) ∨ (¬ p2584) ∨ (¬ p2589) ∨ (¬ p3324))
    : (¬ p2383) ∨ (¬ p2295) ∨ (¬ p2584) ∨ p2668 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2584 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43209 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79455 (p2274 p2312 p2449 p3516 p3947 p4067 p4564 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h41245 : (¬ p2274) ∨ (¬ p2312) ∨ (¬ p3516) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4564))
    : (¬ p3516) ∨ (¬ p2312) ∨ (¬ p4067) ∨ p2449 ∨ (¬ p2274) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2312 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41245 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step79456 (p2177 p2264 p2553 p3553 p4067 p4973 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h41405 : (¬ p2177) ∨ (¬ p2553) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4973))
    : (¬ p2553) ∨ (¬ p2177) ∨ p2264 ∨ (¬ p4973) ∨ (¬ p4067) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41405 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79457 (p2264 p2881 p3553 p3564 p3984 p4067 p4275 p4624 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h49710 : (¬ p2881) ∨ (¬ p3553) ∨ (¬ p3564) ∨ (¬ p3984) ∨ (¬ p4067) ∨ (¬ p4275) ∨ (¬ p4624))
    : (¬ p3564) ∨ (¬ p3984) ∨ p2264 ∨ (¬ p4275) ∨ (¬ p4067) ∨ (¬ p2881) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4275 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h49710 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (False.elim (r5 u6)))))))))))))))

theorem step79458 (p2396 p2449 p2668 p3947 p4067 p4405 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h54891 : (¬ p2396) ∨ (¬ p2668) ∨ (¬ p3947) ∨ (¬ p4067) ∨ (¬ p4405))
    : (¬ p2668) ∨ (¬ p2396) ∨ (¬ p4067) ∨ (¬ p4405) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54891 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79462 (p2177 p2264 p3323 p3553 p4067 p4624 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h51362 : (¬ p2177) ∨ (¬ p3323) ∨ (¬ p3553) ∨ (¬ p4067) ∨ (¬ p4624))
    : (¬ p3323) ∨ (¬ p4067) ∨ p2264 ∨ (¬ p2177) ∨ (¬ p4624) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4624 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h51362 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79465 (p2331 p2807 p2963 p4067 : Prop)
    (h73338 : p2963 ∨ p2331)
    (h6052 : (¬ p2807) ∨ (¬ p2963) ∨ (¬ p4067))
    : p2331 ∨ (¬ p4067) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p4067 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6052 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79467 (p2274 p2295 p3568 p3986 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h20288 : (¬ p2274) ∨ (¬ p3568) ∨ (¬ p3986))
    : p2295 ∨ (¬ p2274) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20288 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step79472 (p2563 p2668 p3063 p3309 p3324 p3549 p3986 p4110 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h73516 : p4110 ∨ p2563)
    (h73406 : p3549 ∨ p3309)
    (h46205 : (¬ p3063) ∨ (¬ p3324) ∨ (¬ p3549) ∨ (¬ p3986) ∨ (¬ p4110))
    : (¬ p3063) ∨ (¬ p3986) ∨ p2668 ∨ p2563 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46205 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79473 (p2187 p2668 p3324 p3986 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h6004 : (¬ p2187) ∨ (¬ p3324) ∨ (¬ p3986))
    : p2668 ∨ (¬ p2187) ∨ (¬ p3986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6004 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step79480 (p2668 p3125 p3324 p3986 p4345 p5118 p5580 : Prop)
    (h73386 : p3324 ∨ p2668)
    (h49463 : (¬ p3125) ∨ (¬ p3324) ∨ (¬ p3986) ∨ (¬ p4345) ∨ (¬ p5118) ∨ (¬ p5580))
    : (¬ p5580) ∨ (¬ p5118) ∨ (¬ p4345) ∨ p2668 ∨ (¬ p3986) ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5580 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4345 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3986 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49463 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (False.elim (r4 u0)))))))))))))

theorem step79484 (p3083 p3343 p3359 p4045 p4256 : Prop)
    (h73387 : (¬ p3343) ∨ (¬ p3359))
    (h73542 : p4256 ∨ p3083)
    (h24642 : p3359 ∨ (¬ p4045) ∨ (¬ p4256))
    : (¬ p4045) ∨ (¬ p3343) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4045 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3359) := (Or.elim h73387 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h24642 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u4)))))))

theorem step79488 (p3016 p4971 p4972 : Prop)
    (h73858 : p4971 ∨ p3016)
    (h8275 : (¬ p4971) ∨ p4972)
    : p3016 ∨ p4972 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4972) := (fun h => hn (Or.inr h));
    let u2 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8275 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79489 (p3016 p4971 p4973 : Prop)
    (h73858 : p4971 ∨ p3016)
    (h8276 : (¬ p4971) ∨ p4973)
    : p3016 ∨ p4973 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4973) := (fun h => hn (Or.inr h));
    let u2 : p4971 := (Or.elim h73858 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8276 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79490 (p2363 p2528 p2668 p3324 p3875 p3920 p4347 p4973 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73386 : p3324 ∨ p2668)
    (h41465 : (¬ p2528) ∨ (¬ p3324) ∨ (¬ p3875) ∨ (¬ p3920) ∨ (¬ p4347) ∨ (¬ p4973))
    : (¬ p3920) ∨ p2363 ∨ (¬ p4973) ∨ (¬ p3875) ∨ p2668 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3920 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41465 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step79491 (p2761 p2911 p3192 p3276 p3644 p4381 p4668 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73434 : p3644 ∨ p2911)
    (h49641 : (¬ p3192) ∨ (¬ p3276) ∨ (¬ p3644) ∨ (¬ p4381) ∨ (¬ p4668))
    : p2761 ∨ (¬ p3192) ∨ (¬ p3276) ∨ p2911 ∨ (¬ p4668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49641 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79494 (p2459 p4445 p4665 : Prop)
    (h73696 : p4665 ∨ p2459)
    (h7480 : p4445 ∨ (¬ p4665))
    : p4445 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4445) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7480 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step79495 (p2459 p4665 p4666 : Prop)
    (h73696 : p4665 ∨ p2459)
    (h7482 : (¬ p4665) ∨ p4666)
    : p2459 ∨ p4666 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4666) := (fun h => hn (Or.inr h));
    let u2 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7482 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79496 (p2459 p3950 p4665 : Prop)
    (h73696 : p4665 ∨ p2459)
    (h7483 : p3950 ∨ (¬ p4665))
    : p3950 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3950) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : p4665 := (Or.elim h73696 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7483 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step79502 (p2440 p3016 p3125 p3564 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h43023 : (¬ p2440) ∨ (¬ p3016) ∨ (¬ p3564) ∨ (¬ p3744))
    : (¬ p3564) ∨ p3125 ∨ (¬ p3016) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43023 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79503 (p3096 p3125 p3564 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h26007 : (¬ p3096) ∨ (¬ p3564) ∨ (¬ p3744))
    : (¬ p3564) ∨ p3125 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h26007 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step79506 (p2363 p3564 p4347 p4604 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h50033 : (¬ p3564) ∨ (¬ p4347) ∨ p4604)
    : p4604 ∨ (¬ p3564) ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4604) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50033 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (u0 r1)))))))

theorem step79507 (p2284 p2553 p2588 p3125 p3564 p3744 p3952 p4700 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73282 : p2588 ∨ p2553)
    (h73496 : p3952 ∨ p2284)
    (h48612 : (¬ p2588) ∨ (¬ p3564) ∨ (¬ p3744) ∨ (¬ p3952) ∨ (¬ p4700))
    : (¬ p3564) ∨ p3125 ∨ p2553 ∨ p2284 ∨ (¬ p4700) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4700 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48612 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79512 (p2284 p2553 p2588 p3115 p3564 p4033 p4208 : Prop)
    (h73534 : p4208 ∨ p3115)
    (h73282 : p2588 ∨ p2553)
    (h45372 : (¬ p2284) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4033) ∨ (¬ p4208))
    : p3115 ∨ (¬ p3564) ∨ p2553 ∨ (¬ p4033) ∨ (¬ p2284) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4033 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2284 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4208 := (Or.elim h73534 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45372 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79515 (p2274 p2761 p3096 p3097 p3461 p3564 p4381 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73352 : p3097 ∨ p2274)
    (h44361 : (¬ p3096) ∨ (¬ p3097) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4381))
    : p2761 ∨ (¬ p3461) ∨ (¬ p3096) ∨ (¬ p3564) ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44361 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79517 (p2264 p2807 p2911 p3564 p3581 p3644 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h59106 : (¬ p2264) ∨ (¬ p2807) ∨ (¬ p3564) ∨ (¬ p3581) ∨ (¬ p3644))
    : p2911 ∨ (¬ p2264) ∨ (¬ p3581) ∨ (¬ p3564) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h59106 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79518 (p2274 p2449 p3096 p3097 p3564 p3947 p4623 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73494 : p3947 ∨ p2449)
    (h71430 : (¬ p4623) ∨ (¬ p3947) ∨ (¬ p3097) ∨ (¬ p3096) ∨ (¬ p3564))
    : (¬ p3564) ∨ (¬ p4623) ∨ p2274 ∨ (¬ p3096) ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4623 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2449) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h71430 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79519 (p2274 p2553 p2588 p3323 p3564 p4037 p4564 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73282 : p2588 ∨ p2553)
    (h41594 : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4564))
    : (¬ p3564) ∨ p3323 ∨ p2553 ∨ (¬ p2274) ∨ (¬ p4564) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41594 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79520 (p2274 p2553 p2588 p3461 p3564 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h46319 : (¬ p2274) ∨ (¬ p2588) ∨ (¬ p3461) ∨ (¬ p3564))
    : (¬ p3564) ∨ (¬ p3461) ∨ p2553 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46319 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79521 (p2363 p2774 p2780 p2911 p3367 p3389 p3609 p3759 p4078 p4340 p4503 p4734 : Prop)
    (h73558 : p4340 ∨ p3609)
    (h73308 : p2780 ∨ p2774)
    (h72735 : p4734)
    (h54283 : (¬ p2363) ∨ (¬ p2780) ∨ (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3759) ∨ (¬ p4078) ∨ (¬ p4340) ∨ (¬ p4503) ∨ (¬ p4734))
    : p3609 ∨ p2774 ∨ (¬ p2911) ∨ (¬ p2363) ∨ (¬ p3759) ∨ (¬ p4503) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p4078) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2774) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4503 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4078 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4340 := (Or.elim h73558 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p2780 := (Or.elim h73308 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p4734 := h72735;
    (Or.elim h54283 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u5))) (fun r8 => (False.elim (r8 u11)))))))))))))))))))))

theorem step79523 (p2440 p2542 p3266 p3276 p3343 p3359 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73388 : p3359 ∨ p3343)
    (h73270 : p2542 ∨ p2440)
    (h45506 : (¬ p2542) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3266) ∨ p3343 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45506 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79525 (p2630 p2810 p3266 p3276 p3343 p3359 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73388 : p3359 ∨ p3343)
    (h73316 : p2810 ∨ p2630)
    (h43620 : (¬ p2810) ∨ (¬ p3266) ∨ (¬ p3359) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3266) ∨ p3343 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3343) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43620 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79526 (p2662 p2727 p2761 p3276 p3346 p4111 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73518 : p4111 ∨ p2727)
    (h48489 : (¬ p2662) ∨ (¬ p2761) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425))
    : p3276 ∨ (¬ p2761) ∨ (¬ p2662) ∨ (¬ p3346) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48489 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79527 (p2662 p2727 p3266 p3276 p3346 p4111 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73518 : p4111 ∨ p2727)
    (h60287 : (¬ p2662) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4111) ∨ (¬ p4425))
    : p3276 ∨ (¬ p3266) ∨ (¬ p2662) ∨ (¬ p3346) ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2727) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60287 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79531 (p3016 p3276 p3343 p3359 p3461 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73388 : p3359 ∨ p3343)
    (h54914 : (¬ p3016) ∨ (¬ p3359) ∨ (¬ p3461) ∨ (¬ p4425))
    : p3276 ∨ p3343 ∨ (¬ p3461) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h54914 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79533 (p2459 p3276 p3461 p4045 p4171 p4420 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h58566 : (¬ p2459) ∨ (¬ p3461) ∨ (¬ p4045) ∨ (¬ p4171) ∨ (¬ p4420) ∨ (¬ p4425))
    : p3276 ∨ (¬ p4171) ∨ (¬ p2459) ∨ (¬ p4045) ∨ (¬ p3461) ∨ (¬ p4420) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4171 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h58566 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step79534 (p3266 p3276 p4425 p4695 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h19888 : (¬ p3266) ∨ (¬ p4425) ∨ (¬ p4695))
    : p3276 ∨ (¬ p3266) ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19888 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step79536 (p2696 p2761 p2797 p3276 p3323 p3346 p4425 p4621 p4729 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h50587 : (¬ p2696) ∨ (¬ p2761) ∨ (¬ p2797) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p4425) ∨ (¬ p4621) ∨ (¬ p4729))
    : p3276 ∨ (¬ p2761) ∨ (¬ p4621) ∨ (¬ p2797) ∨ (¬ p2696) ∨ (¬ p3323) ∨ (¬ p3346) ∨ (¬ p4729) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50587 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step79537 (p2608 p2761 p2829 p3276 p3346 p3483 p4425 p4621 p5193 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h63691 : (¬ p2608) ∨ (¬ p2761) ∨ (¬ p2829) ∨ (¬ p3346) ∨ (¬ p3483) ∨ (¬ p4425) ∨ (¬ p4621) ∨ (¬ p5193))
    : p3276 ∨ (¬ p3483) ∨ (¬ p5193) ∨ (¬ p4621) ∨ (¬ p2608) ∨ (¬ p3346) ∨ (¬ p2761) ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3483 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4621 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2829 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h63691 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step79538 (p2761 p3246 p3276 p4277 p4425 p4635 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h55997 : (¬ p2761) ∨ (¬ p3246) ∨ (¬ p4277) ∨ (¬ p4425) ∨ (¬ p4635))
    : p3276 ∨ (¬ p2761) ∨ (¬ p4635) ∨ (¬ p3246) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55997 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79539 (p3276 p3323 p3461 p3746 p4425 p4976 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h41824 : (¬ p3323) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4976))
    : p3276 ∨ (¬ p3461) ∨ (¬ p3323) ∨ (¬ p3746) ∨ (¬ p4976) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4976 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h41824 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79540 (p2088 p2484 p3266 p3276 p4045 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h54793 : (¬ p2088) ∨ (¬ p2484) ∨ (¬ p3266) ∨ (¬ p4045) ∨ (¬ p4425))
    : p3276 ∨ (¬ p4045) ∨ (¬ p3266) ∨ (¬ p2484) ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4045 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2484 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54793 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79543 (p2132 p2860 p3125 p3266 p3276 p3346 p4330 p4425 p4729 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h50976 : (¬ p2132) ∨ (¬ p2860) ∨ (¬ p3125) ∨ (¬ p3266) ∨ (¬ p3346) ∨ (¬ p4330) ∨ (¬ p4425) ∨ (¬ p4729))
    : p3276 ∨ (¬ p3125) ∨ (¬ p2132) ∨ (¬ p4330) ∨ (¬ p4729) ∨ (¬ p2860) ∨ (¬ p3346) ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2860 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3266 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50976 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u3))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79545 (p2761 p3276 p4425 p4451 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h37717 : (¬ p2761) ∨ (¬ p4425) ∨ (¬ p4451))
    : p3276 ∨ (¬ p4451) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4451 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h37717 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79548 (p2553 p3276 p3461 p3746 p4425 p4620 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h42566 : (¬ p2553) ∨ (¬ p3461) ∨ (¬ p3746) ∨ (¬ p4425) ∨ (¬ p4620))
    : p3276 ∨ (¬ p3461) ∨ (¬ p4620) ∨ (¬ p2553) ∨ (¬ p3746) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3746 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42566 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79555 (p2761 p3276 p3516 p4066 p4425 p4635 p4653 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h55466 : (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4066) ∨ (¬ p4425) ∨ (¬ p4635) ∨ (¬ p4653))
    : p3276 ∨ (¬ p4066) ∨ (¬ p2761) ∨ (¬ p4653) ∨ (¬ p3516) ∨ (¬ p4635) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p4066 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4653 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55466 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79558 (p3266 p4444 p5122 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h47325 : (¬ p4444) ∨ p5122)
    : p3266 ∨ p5122 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5122) := (fun h => hn (Or.inr h));
    let u2 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47325 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79560 (p2459 p3266 p3276 p3358 p4348 p4438 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73562 : p4348 ∨ p2459)
    (h40942 : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3276) ∨ (¬ p4438) ∨ (¬ p3358) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h40942 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79563 (p2192 p2210 p3125 p3266 p3276 p3355 p3555 p3744 p4173 p4444 p4604 p5190 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73454 : p3744 ∨ p3125)
    (h73412 : p3555 ∨ p2210)
    (h73528 : p4173 ∨ p2192)
    (h56280 : (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3555) ∨ (¬ p3744) ∨ (¬ p4173) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5190))
    : (¬ p3276) ∨ p3266 ∨ (¬ p5190) ∨ p3125 ∨ p2210 ∨ p2192 ∨ (¬ p3355) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2192) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4173 := (Or.elim h73528 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h56280 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step79565 (p2470 p2476 p2528 p2534 p3266 p3363 p3367 p3585 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h73428 : p3585 ∨ p3367)
    (h73250 : p2476 ∨ p2470)
    (h45221 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3363) ∨ (¬ p3585) ∨ (¬ p4444))
    : p3266 ∨ p2528 ∨ (¬ p3363) ∨ p3367 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u8 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h45221 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79569 (p3146 p3266 p3276 p3358 p3692 p4434 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h41672 : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p3692) ∨ (¬ p4434) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3276) ∨ (¬ p3358) ∨ p3146 ∨ (¬ p4434) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41672 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79572 (p3146 p3266 p3276 p3692 p3945 p4444 p4636 p4902 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h48625 : (¬ p3276) ∨ (¬ p3692) ∨ (¬ p3945) ∨ (¬ p4444) ∨ (¬ p4636) ∨ (¬ p4902))
    : (¬ p3276) ∨ p3266 ∨ (¬ p4636) ∨ p3146 ∨ (¬ p3945) ∨ (¬ p4902) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3146) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48625 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step79573 (p2509 p2528 p2534 p3266 p3379 p3452 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h42722 : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452) ∨ (¬ p4444))
    : (¬ p2509) ∨ p3266 ∨ p3379 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42722 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79574 (p2528 p2534 p2651 p2657 p3083 p3266 p4256 p4444 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73580 : p4444 ∨ p3266)
    (h73288 : p2657 ∨ p2651)
    (h73542 : p4256 ∨ p3083)
    (h45455 : (¬ p2534) ∨ (¬ p2657) ∨ (¬ p4256) ∨ (¬ p4444))
    : p2528 ∨ p3266 ∨ p2651 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2651) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45455 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79577 (p2470 p2476 p2528 p2534 p2662 p2727 p3266 p4111 p4444 : Prop)
    (h73518 : p4111 ∨ p2727)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73580 : p4444 ∨ p3266)
    (h43621 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p4111) ∨ (¬ p4444))
    : p2727 ∨ p2528 ∨ p2470 ∨ (¬ p2662) ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4111 := (Or.elim h73518 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43621 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step79578 (p2470 p2476 p2528 p2534 p2630 p2662 p2810 p3266 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73316 : p2810 ∨ p2630)
    (h56771 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2662) ∨ (¬ p2810) ∨ (¬ p4444))
    : p3266 ∨ p2528 ∨ p2470 ∨ p2630 ∨ (¬ p2662) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56771 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79580 (p2528 p2534 p2761 p3266 p3945 p4420 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h62932 : (¬ p2534) ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4420) ∨ (¬ p4444))
    : p3266 ∨ (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4420) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4420 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62932 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79588 (p2241 p2470 p2476 p2528 p2534 p2996 p3027 p3266 p3931 p4444 p4826 p5193 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73580 : p4444 ∨ p3266)
    (h73250 : p2476 ∨ p2470)
    (h73340 : p3027 ∨ p2996)
    (h50289 : (¬ p2241) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p3027) ∨ (¬ p3931) ∨ (¬ p4444) ∨ (¬ p4826) ∨ (¬ p5193))
    : p2528 ∨ p3266 ∨ (¬ p4826) ∨ p2470 ∨ (¬ p5193) ∨ (¬ p3931) ∨ (¬ p2241) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3931 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50289 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u10))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79591 (p2470 p2476 p2528 p2534 p2608 p3266 p3347 p3399 p3954 p4075 p4444 p4826 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73498 : p3954 ∨ p2608)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h71432 : (¬ p3399) ∨ (¬ p4075) ∨ (¬ p4444) ∨ (¬ p3347) ∨ (¬ p2476) ∨ (¬ p3954) ∨ (¬ p4826) ∨ (¬ p2534))
    : (¬ p4075) ∨ p3266 ∨ p2608 ∨ (¬ p4826) ∨ (¬ p3347) ∨ p2528 ∨ p2470 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4075 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2608) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3954 := (Or.elim h73498 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h71432 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u3))) (fun r6 => (False.elim (r6 u10)))))))))))))))))

theorem step79595 (p2132 p2470 p2476 p2528 p2534 p2870 p3266 p4129 p4444 p4729 p4826 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h62891 : (¬ p2132) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2870) ∨ (¬ p4129) ∨ (¬ p4444) ∨ (¬ p4729) ∨ (¬ p4826))
    : (¬ p4129) ∨ p3266 ∨ (¬ p4826) ∨ p2470 ∨ p2528 ∨ (¬ p2870) ∨ (¬ p4729) ∨ (¬ p2132) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4129 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2870 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4729 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2132 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62891 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step79598 (p2210 p2608 p3105 p3266 p3276 p3355 p3519 p3555 p4376 p4385 p4418 p4444 p5059 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73412 : p3555 ∨ p2210)
    (h73576 : p4385 ∨ p3105)
    (h56221 : (¬ p2608) ∨ (¬ p3276) ∨ (¬ p3355) ∨ (¬ p3519) ∨ (¬ p3555) ∨ (¬ p4376) ∨ (¬ p4385) ∨ (¬ p4418) ∨ (¬ p4444) ∨ (¬ p5059))
    : p3266 ∨ (¬ p4418) ∨ (¬ p2608) ∨ (¬ p5059) ∨ p2210 ∨ (¬ p3355) ∨ (¬ p4376) ∨ (¬ p3519) ∨ p3105 ∨ (¬ p3276) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p4418 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3105) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p4385 := (Or.elim h73576 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h56221 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u12))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u1))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step79599 (p2475 p2528 p2534 p2630 p3005 p3177 p3266 p3877 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h73488 : p3877 ∨ p3005)
    (h45369 : (¬ p2475) ∨ (¬ p2534) ∨ (¬ p2630) ∨ (¬ p3177) ∨ (¬ p3877) ∨ (¬ p4444))
    : p3266 ∨ p2528 ∨ (¬ p3177) ∨ (¬ p2475) ∨ (¬ p2630) ∨ p3005 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2475 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3005) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45369 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step79600 (p2230 p2470 p2476 p2528 p2534 p3266 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h44590 : (¬ p2230) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p4444))
    : p3266 ∨ p2528 ∨ p2470 ∨ (¬ p2230) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2230 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44590 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79605 (p2363 p3266 p3276 p3358 p4347 p4384 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h48488 : (¬ p3276) ∨ (¬ p3358) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3276) ∨ p2363 ∨ (¬ p3358) ∨ (¬ p4384) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3358 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h48488 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79606 (p2246 p2341 p2459 p2651 p2744 p3016 p3266 p3366 p3551 p3820 p3888 p4348 p4444 p5250 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73562 : p4348 ∨ p2459)
    (h73408 : p3551 ∨ p2341)
    (h64141 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2744) ∨ (¬ p3016) ∨ (¬ p3366) ∨ (¬ p3551) ∨ (¬ p3820) ∨ (¬ p3888) ∨ (¬ p4348) ∨ (¬ p4444) ∨ (¬ p5250))
    : (¬ p3888) ∨ p3266 ∨ (¬ p5250) ∨ (¬ p3366) ∨ p2459 ∨ (¬ p2744) ∨ (¬ p3820) ∨ (¬ p2246) ∨ (¬ p2651) ∨ (¬ p3016) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3888 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5250 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3820 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))));
    let u10 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))));
    let u11 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u12 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u13 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u10 r0))));
    (Or.elim h64141 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u8))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u13))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u0))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u12))) (fun r8 => (Or.elim r8 (fun q9 => (False.elim (q9 u11))) (fun r9 => (False.elim (r9 u2)))))))))))))))))))))))

theorem step79608 (p2528 p2534 p2598 p3055 p3266 p3641 p3874 p4444 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73580 : p4444 ∨ p3266)
    (h73484 : p3874 ∨ p3641)
    (h73350 : p3055 ∨ p2598)
    (h46543 : (¬ p2534) ∨ (¬ p3055) ∨ (¬ p3874) ∨ (¬ p4444))
    : p2528 ∨ p3266 ∨ p3641 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46543 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79610 (p3266 p3461 p4171 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h9696 : (¬ p3461) ∨ (¬ p4171) ∨ (¬ p4444))
    : (¬ p4171) ∨ p3266 ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4171 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h9696 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step79611 (p2363 p2761 p3266 p3945 p4133 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h41811 : (¬ p2761) ∨ (¬ p3945) ∨ (¬ p4133) ∨ (¬ p4347) ∨ (¬ p4444))
    : p3266 ∨ (¬ p2761) ∨ p2363 ∨ (¬ p3945) ∨ (¬ p4133) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3945 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4133 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41811 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79612 (p2352 p2363 p3016 p3266 p3574 p3956 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73560 : p4347 ∨ p2363)
    (h73422 : p3574 ∨ p3016)
    (h73500 : p3956 ∨ p2352)
    (h47534 : (¬ p3574) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444))
    : p3266 ∨ p2363 ∨ p3016 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47534 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79613 (p2352 p2363 p2493 p2499 p3266 p3956 p4347 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73260 : p2499 ∨ p2493)
    (h73500 : p3956 ∨ p2352)
    (h73560 : p4347 ∨ p2363)
    (h42869 : (¬ p2499) ∨ (¬ p3956) ∨ (¬ p4347) ∨ (¬ p4444))
    : p3266 ∨ p2493 ∨ p2352 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42869 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79615 (p2459 p2911 p3266 p3389 p3540 p3644 p4348 p4444 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73580 : p4444 ∨ p3266)
    (h73402 : p3540 ∨ p3389)
    (h73562 : p4348 ∨ p2459)
    (h44532 : (¬ p3540) ∨ (¬ p3644) ∨ (¬ p4348) ∨ (¬ p4444))
    : p2911 ∨ p3266 ∨ p3389 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44532 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79616 (p2341 p2437 p3146 p3266 p3551 p3692 p3742 p4042 p4279 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73448 : p3692 ∨ p3146)
    (h73452 : p3742 ∨ p2437)
    (h73408 : p3551 ∨ p2341)
    (h45566 : (¬ p3551) ∨ (¬ p3692) ∨ (¬ p3742) ∨ (¬ p4042) ∨ (¬ p4279) ∨ (¬ p4444))
    : p3266 ∨ p3146 ∨ p2437 ∨ (¬ p4042) ∨ (¬ p4279) ∨ p2341 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4042 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3692 := (Or.elim h73448 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h45566 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u6)))))))))))))

theorem step79617 (p2761 p3266 p4381 p4444 p4445 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73573 : (¬ p2761) ∨ (¬ p4381))
    (h23297 : p4381 ∨ (¬ p4444) ∨ (¬ p4445))
    : p3266 ∨ (¬ p4445) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p4445 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : (¬ p4381) := (Or.elim h73573 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h23297 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79619 (p2177 p2299 p2396 p2761 p3266 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73234 : p2299 ∨ p2177)
    (h45071 : (¬ p2299) ∨ (¬ p2396) ∨ (¬ p2761) ∨ (¬ p4444))
    : (¬ p2396) ∨ p3266 ∨ (¬ p2761) ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45071 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79622 (p2761 p3051 p3246 p3266 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h46728 : (¬ p2761) ∨ (¬ p3051) ∨ (¬ p3246) ∨ (¬ p4444))
    : (¬ p2761) ∨ p3266 ∨ (¬ p3246) ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46728 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79625 (p2774 p2819 p3266 p3461 p3990 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h46818 : (¬ p2774) ∨ (¬ p2819) ∨ (¬ p3461) ∨ (¬ p3990) ∨ (¬ p4444))
    : p3266 ∨ (¬ p2819) ∨ (¬ p2774) ∨ (¬ p3990) ∨ (¬ p3461) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3990 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46818 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79626 (p2668 p3266 p3323 p3324 p3461 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73386 : p3324 ∨ p2668)
    (h65266 : (¬ p3323) ∨ (¬ p3324) ∨ (¬ p3461) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3461) ∨ p2668 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h65266 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79627 (p2331 p3266 p3323 p3461 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h55618 : (¬ p2331) ∨ (¬ p3323) ∨ (¬ p3461) ∨ (¬ p4444))
    : (¬ p3461) ∨ p3266 ∨ (¬ p2331) ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3323 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h55618 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79630 (p2797 p3266 p3461 p3567 p3654 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h60726 : (¬ p2797) ∨ (¬ p3461) ∨ (¬ p3567) ∨ (¬ p3654) ∨ (¬ p4444))
    : (¬ p3567) ∨ p3266 ∨ (¬ p3654) ∨ (¬ p3461) ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3567 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3654 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2797 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60726 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79633 (p2187 p2274 p2459 p3266 p3989 p4138 p4348 p4444 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73580 : p4444 ∨ p3266)
    (h73502 : p3989 ∨ p2187)
    (h43274 : (¬ p2274) ∨ (¬ p3989) ∨ (¬ p4138) ∨ (¬ p4348) ∨ (¬ p4444))
    : p2459 ∨ (¬ p4138) ∨ p3266 ∨ (¬ p2274) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p4138 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43274 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step79634 (p2192 p3125 p3266 p3461 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h45720 : (¬ p2192) ∨ (¬ p3125) ∨ (¬ p3461) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3461) ∨ (¬ p3125) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45720 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79637 (p2553 p2588 p3266 p3461 p3564 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73282 : p2588 ∨ p2553)
    (h63625 : (¬ p2588) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3461) ∨ (¬ p3564) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h63625 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79638 (p2573 p3266 p3461 p3564 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h46966 : (¬ p2573) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h46966 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79639 (p2187 p3096 p3266 p3461 p3564 p3989 p4444 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73502 : p3989 ∨ p2187)
    (h43556 : (¬ p3096) ∨ (¬ p3461) ∨ (¬ p3564) ∨ (¬ p3989) ∨ (¬ p4444))
    : p3266 ∨ (¬ p3461) ∨ (¬ p3564) ∨ p2187 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3461 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43556 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79640 (p2241 p2247 p2641 p2761 p3266 p3323 p3516 p4037 p4154 p4444 p4521 p4604 p4988 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73526 : p4154 ∨ p2641)
    (h73226 : p2247 ∨ p2241)
    (h73508 : p4037 ∨ p3323)
    (h51795 : (¬ p2247) ∨ (¬ p2761) ∨ (¬ p3516) ∨ (¬ p4037) ∨ (¬ p4154) ∨ (¬ p4444) ∨ (¬ p4521) ∨ (¬ p4604) ∨ (¬ p4988))
    : p3266 ∨ (¬ p2761) ∨ (¬ p4604) ∨ p2641 ∨ (¬ p3516) ∨ p2241 ∨ (¬ p4988) ∨ (¬ p4521) ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2241) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4154 := (Or.elim h73526 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p2247 := (Or.elim h73226 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h51795 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u12))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step79643 (p2139 p2598 p2761 p3055 p3266 p3422 p3516 p3564 p3584 p4137 p4444 p4604 p4988 : Prop)
    (h73580 : p4444 ∨ p3266)
    (h73524 : p4137 ∨ p3564)
    (h73426 : p3584 ∨ p3422)
    (h73350 : p3055 ∨ p2598)
    (h56204 : (¬ p2139) ∨ (¬ p2761) ∨ (¬ p3055) ∨ (¬ p3516) ∨ (¬ p3584) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p4988))
    : p3266 ∨ (¬ p3516) ∨ p3564 ∨ (¬ p2761) ∨ p3422 ∨ (¬ p2139) ∨ p2598 ∨ (¬ p4988) ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2139 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2598) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4988 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p3055 := (Or.elim h73350 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h56204 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u12))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step79649 (p2509 p2573 p2579 p3347 p3573 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h24508 : p2509 ∨ (¬ p2579) ∨ (¬ p3347) ∨ (¬ p3573))
    : p2509 ∨ p2573 ∨ (¬ p3573) ∨ (¬ p3347) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2509) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3347 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h24508 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step79654 (p2509 p3083 p4116 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h39385 : p2509 ∨ (¬ p4116) ∨ (¬ p4256))
    : p2509 ∨ (¬ p4116) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2509) := (fun h => hn (Or.inl h));
    let u1 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h39385 (fun q0 => (False.elim (u0 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step79655 (p3379 p3452 p5194 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h48298 : (¬ p3452) ∨ p5194)
    : p3379 ∨ p5194 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5194) := (fun h => hn (Or.inr h));
    let u2 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48298 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79656 (p3379 p3452 p5193 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h48331 : (¬ p3452) ∨ p5193)
    : p3379 ∨ p5193 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p5193) := (fun h => hn (Or.inr h));
    let u2 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h48331 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step79657 (p2406 p2427 p2608 p3238 p3379 p3452 p4235 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73536 : p4235 ∨ p2427)
    (h54231 : (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4235))
    : p3379 ∨ (¬ p2608) ∨ p2406 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54231 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79658 (p2417 p2608 p2922 p2928 p3379 p3452 p4278 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h43510 : (¬ p2608) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278))
    : p2922 ∨ p2417 ∨ (¬ p2608) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43510 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79659 (p2373 p2406 p2608 p3238 p3379 p3452 p3880 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h44011 : (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880))
    : p3379 ∨ p2373 ∨ (¬ p2608) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44011 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79661 (p2493 p2499 p2608 p3379 p3452 p3564 p4137 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73524 : p4137 ∨ p3564)
    (h44435 : (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3452) ∨ (¬ p4137))
    : p2493 ∨ p3379 ∨ (¬ p2608) ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44435 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79663 (p2406 p2440 p2542 p2608 p3238 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73270 : p2542 ∨ p2440)
    (h44858 : (¬ p2542) ∨ (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452))
    : p3379 ∨ (¬ p2608) ∨ p2406 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44858 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79664 (p2406 p2563 p2608 p3238 p3379 p3452 p4110 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h73374 : p3238 ∨ p2406)
    (h60078 : (¬ p2608) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110))
    : p3379 ∨ (¬ p2608) ∨ p2563 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60078 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79668 (p2493 p2499 p2608 p3016 p3379 p3452 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h45480 : (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3016) ∨ (¬ p3452))
    : p2493 ∨ p3379 ∨ (¬ p2608) ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45480 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79669 (p2493 p2499 p2608 p3379 p3422 p3452 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h45490 : (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3422) ∨ (¬ p3452))
    : p2493 ∨ p3379 ∨ (¬ p2608) ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45490 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79670 (p2608 p2911 p2922 p2928 p3379 p3452 p3644 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h73434 : p3644 ∨ p2911)
    (h46669 : (¬ p2608) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3644))
    : (¬ p2608) ∨ p3379 ∨ p2922 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46669 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79671 (p2509 p2528 p2534 p2608 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h50384 : (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2608) ∨ (¬ p3452))
    : (¬ p2509) ∨ p3379 ∨ p2528 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50384 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79676 (p2241 p2493 p2499 p3016 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h45472 : (¬ p2241) ∨ (¬ p2499) ∨ (¬ p3016) ∨ (¬ p3452))
    : (¬ p2241) ∨ p3379 ∨ (¬ p3016) ∨ p2493 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45472 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79679 (p2459 p2608 p2881 p3051 p3193 p3370 p3379 p3452 p4377 p4697 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h60986 : (¬ p2459) ∨ (¬ p2608) ∨ (¬ p2881) ∨ (¬ p3051) ∨ (¬ p3193) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4697))
    : (¬ p2881) ∨ (¬ p3051) ∨ (¬ p2608) ∨ (¬ p2459) ∨ p3379 ∨ (¬ p3370) ∨ (¬ p4377) ∨ (¬ p4697) ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4697 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60986 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (False.elim (r7 u7)))))))))))))))))))

theorem step79690 (p2192 p2210 p2274 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h64916 : (¬ p2192) ∨ (¬ p2210) ∨ (¬ p2274) ∨ (¬ p3452))
    : (¬ p2274) ∨ p3379 ∨ (¬ p2210) ∨ (¬ p2192) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2192 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h64916 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79692 (p2210 p2881 p2891 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h64952 : (¬ p2210) ∨ (¬ p2881) ∨ (¬ p2891) ∨ (¬ p3452))
    : p3379 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h64952 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79693 (p2210 p2891 p3246 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h47940 : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) ∨ (¬ p3452))
    : p3379 ∨ (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47940 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79695 (p2352 p2493 p2499 p2608 p3379 p3452 p3956 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73500 : p3956 ∨ p2352)
    (h44198 : (¬ p2499) ∨ (¬ p2608) ∨ (¬ p3452) ∨ (¬ p3956))
    : p2493 ∨ p3379 ∨ (¬ p2608) ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44198 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79696 (p2210 p2493 p2499 p3379 p3452 p4210 p4715 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h50881 : (¬ p2210) ∨ (¬ p2499) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4715))
    : p3379 ∨ p2493 ∨ (¬ p2210) ∨ (¬ p4715) ∨ (¬ p4210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50881 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79699 (p2166 p2210 p3146 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h47099 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3146) ∨ (¬ p3452))
    : (¬ p3146) ∨ p3379 ∨ (¬ p2210) ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47099 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79704 (p2210 p2509 p3379 p3452 p4210 p4608 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42196 : (¬ p2210) ∨ (¬ p2509) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4608))
    : (¬ p4210) ∨ p3379 ∨ (¬ p2509) ∨ (¬ p4608) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42196 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79705 (p2210 p2440 p3379 p3452 p4210 p4814 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h50092 : (¬ p2210) ∨ (¬ p2440) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4814))
    : p3379 ∨ (¬ p4210) ∨ (¬ p2440) ∨ (¬ p4814) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4814 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h50092 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79708 (p2210 p2850 p3379 p3452 p3684 p4210 p5217 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73442 : p3684 ∨ p2850)
    (h40961 : (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3684) ∨ (¬ p4210) ∨ (¬ p5217))
    : p3379 ∨ (¬ p2210) ∨ p2850 ∨ (¬ p4210) ∨ (¬ p5217) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5217 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h40961 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79709 (p2210 p2427 p2881 p3379 p3452 p4210 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h64885 : (¬ p2210) ∨ (¬ p2427) ∨ (¬ p2881) ∨ (¬ p3452) ∨ (¬ p4210))
    : (¬ p4210) ∨ (¬ p2210) ∨ (¬ p2881) ∨ p3379 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h64885 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79710 (p2210 p2922 p2928 p3379 p3452 p4210 p4644 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h50884 : (¬ p2210) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4210) ∨ (¬ p4644))
    : p3379 ∨ p2922 ∨ (¬ p4210) ∨ (¬ p4644) ∨ (¬ p2210) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50884 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79717 (p2210 p2982 p3379 p3452 p3680 p4210 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h64963 : (¬ p2210) ∨ (¬ p2982) ∨ (¬ p3452) ∨ (¬ p3680) ∨ (¬ p4210))
    : (¬ p2982) ∨ (¬ p3680) ∨ (¬ p4210) ∨ (¬ p2210) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3680 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h64963 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79723 (p2210 p3379 p3422 p3452 p3584 p3590 p4241 p4282 p4715 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73426 : p3584 ∨ p3422)
    (h50354 : (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3584) ∨ (¬ p3590) ∨ (¬ p4241) ∨ (¬ p4282) ∨ (¬ p4715))
    : p3379 ∨ (¬ p3590) ∨ p3422 ∨ (¬ p2210) ∨ (¬ p4241) ∨ (¬ p4715) ∨ (¬ p4282) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4282 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50354 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u6))) (fun r5 => (False.elim (r5 u5)))))))))))))))

theorem step79725 (p2264 p2417 p2685 p2696 p2922 p2928 p3379 p3452 p4278 p4666 p4733 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73320 : p2928 ∨ p2922)
    (h73394 : p3452 ∨ p3379)
    (h49997 : (¬ p2264) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4666) ∨ (¬ p4733))
    : p2417 ∨ (¬ p2264) ∨ p2922 ∨ (¬ p2696) ∨ p3379 ∨ (¬ p2685) ∨ (¬ p4733) ∨ (¬ p4666) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p2264 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4666 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h49997 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step79732 (p2241 p2996 p3027 p3379 p3452 p4116 p4652 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73340 : p3027 ∨ p2996)
    (h42612 : (¬ p2241) ∨ (¬ p3027) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4652))
    : (¬ p2241) ∨ p3379 ∨ (¬ p4116) ∨ (¬ p4652) ∨ p2996 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2996) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3027 := (Or.elim h73340 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42612 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step79733 (p2241 p2641 p3379 p3452 p4116 p4975 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h41386 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4975))
    : (¬ p2241) ∨ p3379 ∨ (¬ p2641) ∨ (¬ p4116) ∨ (¬ p4975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4975 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41386 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79743 (p2241 p2630 p2745 p3379 p3452 p4116 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h41384 : (¬ p2241) ∨ (¬ p2630) ∨ (¬ p2745) ∨ (¬ p3452) ∨ (¬ p4116))
    : (¬ p2241) ∨ p3379 ∨ (¬ p4116) ∨ (¬ p2745) ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2745 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h41384 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step79744 (p2241 p2406 p2440 p2542 p3238 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73270 : p2542 ∨ p2440)
    (h44854 : (¬ p2241) ∨ (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3452))
    : (¬ p2241) ∨ p3379 ∨ p2406 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44854 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79748 (p2241 p2992 p3379 p3452 p4116 p4704 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73046 : p4704)
    (h41317 : (¬ p2241) ∨ (¬ p2992) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p4704))
    : (¬ p2241) ∨ p3379 ∨ (¬ p2992) ∨ (¬ p4116) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2992 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4704 := h73046;
    (Or.elim h41317 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step79749 (p2241 p2509 p2528 p2534 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h47793 : (¬ p2241) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p3452))
    : (¬ p2509) ∨ p3379 ∨ (¬ p2241) ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2509 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47793 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79750 (p2449 p2509 p2528 p2534 p2685 p2696 p3379 p3452 p3950 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h49800 : (¬ p2449) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2685) ∨ (¬ p2696) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733))
    : (¬ p2449) ∨ p3379 ∨ (¬ p2696) ∨ (¬ p2509) ∨ (¬ p2685) ∨ (¬ p3950) ∨ p2528 ∨ (¬ p4733) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h49800 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u9))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step79753 (p2241 p3193 p3276 p3379 p3452 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73394 : p3452 ∨ p3379)
    (h65274 : (¬ p2241) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p4425))
    : (¬ p3193) ∨ p3276 ∨ (¬ p2241) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3193 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65274 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79755 (p2241 p3189 p3379 p3452 p4116 p5011 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42231 : (¬ p2241) ∨ (¬ p3189) ∨ (¬ p3452) ∨ (¬ p4116) ∨ (¬ p5011))
    : (¬ p2241) ∨ p3379 ∨ (¬ p3189) ∨ (¬ p4116) ∨ (¬ p5011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3189 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5011 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42231 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79756 (p2241 p3379 p3452 p3842 p4116 p5177 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42233 : (¬ p2241) ∨ (¬ p3452) ∨ (¬ p3842) ∨ (¬ p4116) ∨ (¬ p5177))
    : (¬ p2241) ∨ p3379 ∨ (¬ p4116) ∨ (¬ p3842) ∨ (¬ p5177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4116 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3842 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h42233 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79757 (p2331 p2363 p2668 p2963 p3324 p3366 p3379 p3399 p3452 p3631 p3950 p4236 p4347 p4376 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73338 : p2963 ∨ p2331)
    (h73394 : p3452 ∨ p3379)
    (h73386 : p3324 ∨ p2668)
    (h53525 : (¬ p2963) ∨ (¬ p3324) ∨ (¬ p3366) ∨ (¬ p3399) ∨ (¬ p3452) ∨ (¬ p3631) ∨ (¬ p3950) ∨ (¬ p4236) ∨ (¬ p4347) ∨ (¬ p4376))
    : (¬ p3631) ∨ p2363 ∨ (¬ p3399) ∨ (¬ p4236) ∨ (¬ p3366) ∨ (¬ p3950) ∨ p2331 ∨ p3379 ∨ (¬ p4376) ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3399 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2331) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p2963 := (Or.elim h73338 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u13 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h53525 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u13))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u0))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u5))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u3))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u8)))))))))))))))))))))

theorem step79760 (p2098 p2363 p2373 p2922 p2928 p3379 p3452 p3609 p3741 p3880 p4134 p4347 p4733 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73490 : p3880 ∨ p2373)
    (h73394 : p3452 ∨ p3379)
    (h73320 : p2928 ∨ p2922)
    (h49781 : (¬ p2098) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p3609) ∨ (¬ p3741) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4347) ∨ (¬ p4733))
    : p2363 ∨ (¬ p2098) ∨ (¬ p3741) ∨ p2373 ∨ p3379 ∨ (¬ p4733) ∨ (¬ p4134) ∨ (¬ p3609) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2098 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3609 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h49781 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u5)))))))))))))))))))

theorem step79764 (p2177 p3093 p3309 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h47943 : (¬ p2177) ∨ (¬ p3093) ∨ (¬ p3309) ∨ (¬ p3452))
    : (¬ p3309) ∨ (¬ p3093) ∨ p3379 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47943 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79765 (p2396 p2417 p2922 p2928 p3379 p3452 p4278 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h44936 : (¬ p2396) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278))
    : p2922 ∨ p2417 ∨ (¬ p2396) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2922) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44936 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79766 (p2122 p2396 p2509 p2528 p2534 p2774 p3379 p3452 p3950 p4733 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73268 : p2534 ∨ p2528)
    (h62227 : (¬ p2122) ∨ (¬ p2396) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2774) ∨ (¬ p3452) ∨ (¬ p3950) ∨ (¬ p4733))
    : (¬ p2396) ∨ (¬ p2122) ∨ p3379 ∨ (¬ p2774) ∨ (¬ p4733) ∨ p2528 ∨ (¬ p3950) ∨ (¬ p2509) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3950 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h62227 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79770 (p2417 p2922 p2928 p3246 p3379 p3452 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73320 : p2928 ∨ p2922)
    (h73394 : p3452 ∨ p3379)
    (h45547 : (¬ p2928) ∨ (¬ p3246) ∨ (¬ p3452) ∨ (¬ p4278))
    : p2417 ∨ p2922 ∨ p3379 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45547 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79771 (p2187 p2248 p2284 p2493 p2499 p2553 p2588 p2946 p3379 p3452 p4405 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73282 : p2588 ∨ p2553)
    (h73394 : p3452 ∨ p3379)
    (h61772 : (¬ p2187) ∨ (¬ p2248) ∨ (¬ p2284) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p2946) ∨ (¬ p3452) ∨ (¬ p4405))
    : (¬ p2284) ∨ p2493 ∨ p2553 ∨ (¬ p2248) ∨ p3379 ∨ (¬ p2946) ∨ (¬ p4405) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2493) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2946 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4405 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61772 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step79774 (p2248 p2331 p2363 p2406 p2668 p2982 p3238 p3379 p3452 p4948 p5059 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73846 : p4948 ∨ p2982)
    (h48595 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4948) ∨ (¬ p5059))
    : (¬ p2668) ∨ p3379 ∨ (¬ p2331) ∨ (¬ p2363) ∨ p2406 ∨ (¬ p5059) ∨ (¬ p2248) ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5059 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h48595 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step79775 (p2248 p2331 p2363 p2417 p2668 p2922 p2928 p3379 p3452 p4278 p4669 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73546 : p4278 ∨ p2417)
    (h73394 : p3452 ∨ p3379)
    (h48573 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p2928) ∨ (¬ p3452) ∨ (¬ p4278) ∨ (¬ p4669))
    : (¬ p2668) ∨ (¬ p2331) ∨ p2922 ∨ (¬ p2363) ∨ p2417 ∨ (¬ p4669) ∨ p3379 ∨ (¬ p2248) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2417) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4669 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48573 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step79777 (p2248 p2331 p2509 p2528 p2534 p2668 p3379 p3452 p3979 p5122 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73394 : p3452 ∨ p3379)
    (h52589 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2509) ∨ (¬ p2534) ∨ (¬ p2668) ∨ (¬ p3452) ∨ (¬ p3979) ∨ (¬ p5122))
    : (¬ p2668) ∨ (¬ p2509) ∨ (¬ p5122) ∨ (¬ p2248) ∨ (¬ p2331) ∨ p2528 ∨ (¬ p3979) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3979 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h52589 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u9))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u6))) (fun r6 => (False.elim (r6 u2)))))))))))))))))

theorem step79782 (p2383 p3379 p3452 p3923 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h66683 : (¬ p3452) ∨ (¬ p3923) ∨ (¬ p2383))
    : (¬ p2383) ∨ p3379 ∨ (¬ p3923) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3923 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h66683 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u0)))))))

theorem step79783 (p2253 p2741 p3286 p3379 p3452 p3848 p4376 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h42232 : (¬ p2253) ∨ (¬ p2741) ∨ (¬ p3286) ∨ (¬ p3452) ∨ (¬ p3848) ∨ (¬ p4376))
    : (¬ p3848) ∨ (¬ p2253) ∨ (¬ p3286) ∨ (¬ p4376) ∨ p3379 ∨ (¬ p2741) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3848 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2253 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3286 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2741 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h42232 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u3)))))))))))))

theorem step79785 (p2156 p2284 p2911 p2922 p2928 p3156 p3379 p3452 p3644 p3952 p4521 p4902 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73320 : p2928 ∨ p2922)
    (h73434 : p3644 ∨ p2911)
    (h73394 : p3452 ∨ p3379)
    (h50428 : (¬ p2156) ∨ (¬ p2928) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p3644) ∨ (¬ p3952) ∨ (¬ p4521) ∨ (¬ p4902))
    : (¬ p3156) ∨ p2284 ∨ (¬ p4521) ∨ p2922 ∨ (¬ p4902) ∨ p2911 ∨ (¬ p2156) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2284) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4902 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h50428 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u11))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79789 (p2156 p2427 p2563 p3379 p3452 p4110 p4172 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h43302 : (¬ p2156) ∨ (¬ p2427) ∨ (¬ p3452) ∨ (¬ p4110) ∨ (¬ p4172))
    : (¬ p2427) ∨ p3379 ∨ (¬ p2156) ∨ p2563 ∨ (¬ p4172) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4172 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43302 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step79793 (p2241 p2406 p2563 p3238 p3379 p3452 p4110 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h73374 : p3238 ∨ p2406)
    (h43962 : (¬ p2241) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110))
    : (¬ p2241) ∨ p3379 ∨ p2563 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2241 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43962 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79794 (p2187 p2406 p2563 p3238 p3379 p3452 p3989 p4110 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h73502 : p3989 ∨ p2187)
    (h73374 : p3238 ∨ p2406)
    (h44056 : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3989) ∨ (¬ p4110))
    : p3379 ∨ p2563 ∨ p2187 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44056 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79795 (p2274 p2406 p2563 p3097 p3238 p3379 p3452 p4110 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73516 : p4110 ∨ p2563)
    (h73374 : p3238 ∨ p2406)
    (h73352 : p3097 ∨ p2274)
    (h44031 : (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4110))
    : p3379 ∨ p2563 ∨ p2406 ∨ p2274 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44031 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79797 (p2210 p2427 p2891 p3379 p3452 p4235 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73536 : p4235 ∨ p2427)
    (h46561 : (¬ p2210) ∨ (¬ p2891) ∨ (¬ p3452) ∨ (¬ p4235))
    : p3379 ∨ (¬ p2210) ∨ (¬ p2891) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2891 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46561 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79798 (p2406 p2427 p2881 p3238 p3379 p3452 p3570 p4235 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73536 : p4235 ∨ p2427)
    (h73418 : p3570 ∨ p2881)
    (h73374 : p3238 ∨ p2406)
    (h43892 : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3570) ∨ (¬ p4235))
    : p3379 ∨ p2427 ∨ p2881 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43892 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79800 (p2406 p2427 p3238 p3246 p3379 p3452 p3690 p4235 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73446 : p3690 ∨ p3246)
    (h73536 : p4235 ∨ p2427)
    (h73374 : p3238 ∨ p2406)
    (h43539 : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3690) ∨ (¬ p4235))
    : p3379 ∨ p3246 ∨ p2427 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43539 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79801 (p2177 p2299 p2493 p2499 p2553 p2588 p3379 p3452 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h43889 : (¬ p2299) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452))
    : p2493 ∨ p3379 ∨ p2177 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43889 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79803 (p2396 p2493 p2499 p2553 p2588 p3379 p3452 p4107 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73282 : p2588 ∨ p2553)
    (h73514 : p4107 ∨ p2396)
    (h44182 : (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452) ∨ (¬ p4107))
    : p2493 ∨ p3379 ∨ p2553 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2396) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44182 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u7)))))))))

theorem step79808 (p2274 p2493 p2499 p2553 p2588 p3379 p3452 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73282 : p2588 ∨ p2553)
    (h45471 : (¬ p2274) ∨ (¬ p2499) ∨ (¬ p2588) ∨ (¬ p3452))
    : p2493 ∨ p3379 ∨ p2553 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45471 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79810 (p2493 p2499 p3125 p3379 p3452 p3564 p4137 : Prop)
    (h73260 : p2499 ∨ p2493)
    (h73394 : p3452 ∨ p3379)
    (h73524 : p4137 ∨ p3564)
    (h44186 : (¬ p2499) ∨ (¬ p3125) ∨ (¬ p3452) ∨ (¬ p4137))
    : p2493 ∨ (¬ p3125) ∨ p3379 ∨ p3564 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2493) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44186 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79813 (p2307 p2506 p3309 p3379 p3452 p3549 p5020 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73394 : p3452 ∨ p3379)
    (h54036 : (¬ p2307) ∨ (¬ p2506) ∨ (¬ p3452) ∨ (¬ p3549) ∨ (¬ p5020))
    : (¬ p5020) ∨ (¬ p2307) ∨ (¬ p2506) ∨ p3309 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p5020 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2506 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h54036 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step79816 (p2187 p2274 p2307 p2509 p2608 p2962 p3097 p3370 p3379 p3452 p4377 p4384 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73394 : p3452 ∨ p3379)
    (h52625 : (¬ p2187) ∨ (¬ p2307) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2962) ∨ (¬ p3097) ∨ (¬ p3370) ∨ (¬ p3452) ∨ (¬ p4377) ∨ (¬ p4384))
    : p2274 ∨ (¬ p3370) ∨ (¬ p2187) ∨ (¬ p4384) ∨ p3379 ∨ (¬ p2307) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p4377) ∨ (¬ p2962) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p3370 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2307 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4377 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2962 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h52625 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u8))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step79820 (p2493 p2499 p2761 p3266 p3379 p3452 p3516 p3564 p4137 p4444 p4604 p5207 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73260 : p2499 ∨ p2493)
    (h73580 : p4444 ∨ p3266)
    (h73524 : p4137 ∨ p3564)
    (h51790 : (¬ p2499) ∨ (¬ p2761) ∨ (¬ p3452) ∨ (¬ p3516) ∨ (¬ p4137) ∨ (¬ p4444) ∨ (¬ p4604) ∨ (¬ p5207))
    : p3379 ∨ (¬ p5207) ∨ (¬ p2761) ∨ p2493 ∨ p3266 ∨ (¬ p3516) ∨ p3564 ∨ (¬ p4604) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p5207 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3516 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4604 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h51790 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u11))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (False.elim (r6 u1)))))))))))))))))

theorem step79823 (p2248 p2331 p2363 p2373 p2406 p3238 p3256 p3379 p3452 p3880 p4134 p4341 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h73394 : p3452 ∨ p3379)
    (h48569 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3238) ∨ (¬ p3256) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4134) ∨ (¬ p4341) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3256) ∨ (¬ p2248) ∨ (¬ p2331) ∨ p2406 ∨ p2373 ∨ p3379 ∨ (¬ p4134) ∨ (¬ p4341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p4134 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4341 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u12 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48569 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u7))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (False.elim (r7 u9)))))))))))))))))))

theorem step79827 (p2156 p2177 p2274 p2528 p3073 p3379 p3452 p3453 p4261 p4438 p4521 : Prop)
    (h73544 : p4261 ∨ p3073)
    (h73394 : p3452 ∨ p3379)
    (h54265 : (¬ p2156) ∨ (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2528) ∨ (¬ p3452) ∨ (¬ p3453) ∨ (¬ p4261) ∨ (¬ p4438) ∨ (¬ p4521))
    : p3073 ∨ (¬ p2274) ∨ (¬ p4438) ∨ p3379 ∨ (¬ p3453) ∨ (¬ p2528) ∨ (¬ p2156) ∨ (¬ p2177) ∨ (¬ p4521) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3453 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4521 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4261 := (Or.elim h73544 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54265 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u4))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u2))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step79828 (p2248 p2352 p2493 p2499 p2901 p2958 p3051 p3156 p3379 p3452 p3956 p4320 p4433 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73394 : p3452 ∨ p3379)
    (h73500 : p3956 ∨ p2352)
    (h73260 : p2499 ∨ p2493)
    (h59901 : (¬ p2248) ∨ (¬ p2499) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p3956) ∨ (¬ p4320) ∨ (¬ p4433))
    : p2901 ∨ (¬ p3156) ∨ p3379 ∨ (¬ p2958) ∨ p2352 ∨ (¬ p2248) ∨ p2493 ∨ (¬ p3051) ∨ (¬ p4433) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4433 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u11 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u12 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h59901 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u12))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u10))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u11))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u8)))))))))))))))))))

theorem step79829 (p2246 p2509 p2608 p2744 p2901 p2958 p3051 p3156 p3379 p3452 p4320 p4434 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73394 : p3452 ∨ p3379)
    (h60025 : (¬ p2246) ∨ (¬ p2509) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p2958) ∨ (¬ p3051) ∨ (¬ p3156) ∨ (¬ p3452) ∨ (¬ p4320) ∨ (¬ p4434))
    : p2901 ∨ (¬ p3156) ∨ (¬ p2246) ∨ (¬ p4434) ∨ (¬ p2509) ∨ (¬ p2958) ∨ (¬ p2608) ∨ (¬ p2744) ∨ (¬ p3051) ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4434 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2509 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2744 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h60025 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u1))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u11))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u10))) (fun r8 => (False.elim (r8 u3)))))))))))))))))))))

theorem step79832 (p2122 p2774 p3193 p3276 p3379 p3452 p3791 p4425 p4733 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73394 : p3452 ∨ p3379)
    (h50344 : (¬ p2122) ∨ (¬ p2774) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4733) ∨ (¬ p4826))
    : p3276 ∨ (¬ p3791) ∨ (¬ p4733) ∨ (¬ p2774) ∨ (¬ p2122) ∨ p3379 ∨ (¬ p4826) ∨ (¬ p3193) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4733 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2122 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h50344 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u1))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u2))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step79833 (p2406 p2440 p2542 p3238 p3343 p3359 p3379 p3452 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73388 : p3359 ∨ p3343)
    (h73270 : p2542 ∨ p2440)
    (h73374 : p3238 ∨ p2406)
    (h48558 : (¬ p2542) ∨ (¬ p3238) ∨ (¬ p3359) ∨ (¬ p3452))
    : p3379 ∨ p3343 ∨ p2440 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48558 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79834 (p2177 p2248 p2295 p2331 p2373 p2406 p3238 p3379 p3452 p3880 p4905 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h48583 : (¬ p2177) ∨ (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4905))
    : (¬ p2295) ∨ p3379 ∨ p2373 ∨ (¬ p2177) ∨ (¬ p4905) ∨ p2406 ∨ (¬ p2248) ∨ (¬ p2331) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4905 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h48583 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u4)))))))))))))))))

theorem step79835 (p2248 p2295 p2331 p3193 p3276 p3379 p3452 p3791 p4425 p4826 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73394 : p3452 ∨ p3379)
    (h56638 : (¬ p2248) ∨ (¬ p2295) ∨ (¬ p2331) ∨ (¬ p3193) ∨ (¬ p3452) ∨ (¬ p3791) ∨ (¬ p4425) ∨ (¬ p4826))
    : p3276 ∨ (¬ p3791) ∨ (¬ p2331) ∨ p3379 ∨ (¬ p2248) ∨ (¬ p4826) ∨ (¬ p3193) ∨ (¬ p2295) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p3791 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4826 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3193 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2295 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56638 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u9))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u1))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step79836 (p2406 p2528 p2534 p3146 p3238 p3379 p3452 p4607 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73268 : p2534 ∨ p2528)
    (h44007 : (¬ p2534) ∨ (¬ p3146) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4607))
    : p3379 ∨ (¬ p4607) ∨ (¬ p3146) ∨ p2406 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p4607 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3146 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2528) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44007 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step79844 (p2373 p2406 p2619 p3238 p3379 p3452 p3880 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73374 : p3238 ∨ p2406)
    (h73490 : p3880 ∨ p2373)
    (h44010 : (¬ p2619) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880))
    : (¬ p2619) ∨ p3379 ∨ p2406 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44010 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step79845 (p2166 p2210 p2373 p3379 p3452 p3880 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h46964 : (¬ p2166) ∨ (¬ p2210) ∨ (¬ p3452) ∨ (¬ p3880))
    : p3379 ∨ (¬ p2210) ∨ p2373 ∨ (¬ p2166) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2166 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46964 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79846 (p2248 p2331 p2363 p2373 p2406 p2668 p3238 p3379 p3452 p3880 p5568 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h73374 : p3238 ∨ p2406)
    (h48599 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p2363) ∨ (¬ p2668) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p5568))
    : (¬ p5568) ∨ p3379 ∨ (¬ p2331) ∨ (¬ p2248) ∨ p2373 ∨ (¬ p2363) ∨ p2406 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5568 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2248 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48599 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u0)))))))))))))))))

theorem step79848 (p2248 p2331 p2373 p2406 p2797 p3005 p3238 p3379 p3452 p3880 p4195 p5063 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73374 : p3238 ∨ p2406)
    (h73394 : p3452 ∨ p3379)
    (h73490 : p3880 ∨ p2373)
    (h54096 : (¬ p2248) ∨ (¬ p2331) ∨ (¬ p3005) ∨ (¬ p3238) ∨ (¬ p3452) ∨ (¬ p3880) ∨ (¬ p4195) ∨ (¬ p5063))
    : (¬ p2248) ∨ p2797 ∨ (¬ p3005) ∨ (¬ p2331) ∨ p2406 ∨ p3379 ∨ (¬ p5063) ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2248 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3005 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2331 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5063 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p2373) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u9 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    let u11 : p3880 := (Or.elim h73490 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h54096 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u10))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u8))) (fun r6 => (False.elim (r6 u6)))))))))))))))))

theorem step79850 (p2406 p2982 p3238 p3379 p3452 p4322 p4948 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73846 : p4948 ∨ p2982)
    (h73374 : p3238 ∨ p2406)
    (h44013 : (¬ p3238) ∨ (¬ p3452) ∨ (¬ p4322) ∨ (¬ p4948))
    : (¬ p4322) ∨ p3379 ∨ p2982 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2982) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4948 := (Or.elim h73846 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44013 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step79851 (p3379 p3449 p3452 p4149 p4181 p4286 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73394 : p3452 ∨ p3379)
    (h47632 : (¬ p3449) ∨ (¬ p3452) ∨ (¬ p4181) ∨ (¬ p4286))
    : (¬ p4181) ∨ (¬ p3449) ∨ p4149 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4181 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3449 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p4149) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47632 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step79855 (p2685 p2807 p3005 p3063 p3093 p3366 p3379 p3414 p3452 p3877 p4236 p4376 p4774 : Prop)
    (h73488 : p3877 ∨ p3005)
    (h73394 : p3452 ∨ p3379)
    (h73392 : p3414 ∨ p2807)
    (h58395 : (¬ p2685) ∨ (¬ p3063) ∨ (¬ p3093) ∨ (¬ p3366) ∨ (¬ p3414) ∨ (¬ p3452) ∨ (¬ p3877) ∨ (¬ p4236) ∨ (¬ p4376) ∨ (¬ p4774))
    : (¬ p3063) ∨ p3005 ∨ (¬ p4376) ∨ (¬ p3366) ∨ (¬ p4774) ∨ (¬ p3093) ∨ (¬ p4236) ∨ p3379 ∨ (¬ p2685) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3063 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3005) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4774 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p4236 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3379) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p3877 := (Or.elim h73488 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    let u12 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u9 r0))));
    (Or.elim h58395 (fun q0 => (False.elim (q0 u8))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u11))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u6))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u4)))))))))))))))))))))

theorem step79856 (p2598 p2608 p3379 p3452 p3590 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h71436 : (¬ p2608) ∨ (¬ p2598) ∨ (¬ p3452) ∨ (¬ p3590))
    : (¬ p3590) ∨ p3379 ∨ (¬ p2608) ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3590 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2598 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h71436 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step79857 (p3093 p3379 p3452 p3590 p3641 p3874 p3922 p3984 p4595 : Prop)
    (h73394 : p3452 ∨ p3379)
    (h73484 : p3874 ∨ p3641)
    (h41714 : (¬ p3093) ∨ (¬ p3452) ∨ (¬ p3590) ∨ (¬ p3874) ∨ (¬ p3922) ∨ (¬ p3984) ∨ (¬ p4595))
    : (¬ p3922) ∨ p3379 ∨ (¬ p3590) ∨ (¬ p4595) ∨ p3641 ∨ (¬ p3984) ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4595 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3641) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3984 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p3093 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3452 := (Or.elim h73394 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u8 : p3874 := (Or.elim h73484 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41714 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (False.elim (r5 u3)))))))))))))))

theorem step79860 (p2922 p2928 p3193 p4635 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h35784 : (¬ p2928) ∨ p3193 ∨ (¬ p4635))
    : p3193 ∨ (¬ p4635) ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p4635 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h35784 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u0 q1))) (fun r1 => (False.elim (r1 u1)))))))

theorem step79862 (p2210 p2241 p2244 p2749 p2807 p2891 p3414 p4877 : Prop)
    (h73224 : p2244 ∨ p2241)
    (h73392 : p3414 ∨ p2807)
    (h67141 : (¬ p2244) ∨ (¬ p4877) ∨ (¬ p3414) ∨ (¬ p2749) ∨ (¬ p2210) ∨ p2891)
    : p2241 ∨ p2891 ∨ (¬ p4877) ∨ (¬ p2749) ∨ (¬ p2210) ∨ p2807 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4877 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2749 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2210 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2807) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2244 := (Or.elim h73224 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p3414 := (Or.elim h73392 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h67141 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (u1 r4)))))))))))))

theorem step79864 (p2992 p3412 p5959 : Prop)
    (h74285 : p2992 ∨ (¬ p5959))
    (h12739 : p3412 ∨ p5959)
    : p3412 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3412) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr h));
    let u2 : (¬ p5959) := (Or.elim h74285 (fun q0 => (False.elim (u1 q0))) (fun r0 => r0));
    (Or.elim h12739 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step79866 (p2264 p2881 p3553 p3570 p4333 : Prop)
    (h73417 : (¬ p2881) ∨ (¬ p3570))
    (h73410 : p3553 ∨ p2264)
    (h28562 : (¬ p3553) ∨ p3570 ∨ (¬ p4333))
    : (¬ p4333) ∨ (¬ p2881) ∨ p2264 :=
  Classical.byContradiction (fun hn =>
    let u0 : p4333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p3570) := (Or.elim h73417 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u4 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h28562 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u3 q1))) (fun r1 => (False.elim (r1 u0)))))))

theorem step79871 (p2449 p3246 p3947 p4333 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h6565 : (¬ p3246) ∨ (¬ p3947) ∨ (¬ p4333))
    : p2449 ∨ (¬ p3246) ∨ (¬ p4333) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h6565 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step79872 (p2246 p2427 p2630 p2651 p2685 p2810 p4235 p4333 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73316 : p2810 ∨ p2630)
    (h62144 : (¬ p2246) ∨ (¬ p2651) ∨ (¬ p2685) ∨ (¬ p2810) ∨ (¬ p4235) ∨ (¬ p4333))
    : (¬ p4333) ∨ p2427 ∨ (¬ p2651) ∨ (¬ p2685) ∨ p2630 ∨ (¬ p2246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4333 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2685 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2630) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2810 := (Or.elim h73316 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62144 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u0)))))))))))))

end ElevenRUP
