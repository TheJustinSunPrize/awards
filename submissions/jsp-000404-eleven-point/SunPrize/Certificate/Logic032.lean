import Init
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace ElevenRUP

theorem step73654 (p2341 p3551 p4586 p4589 : Prop)
    (h66347 : p4589 ∨ p4586)
    (h7292 : p3551 ∨ (¬ p4586))
    (h9121 : (¬ p2341) ∨ (¬ p3551))
    : p4589 ∨ (¬ p2341) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4589) := (fun h => hn (Or.inl h));
    let u1 : p2341 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4586 := (Or.elim h66347 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3551 := (Or.elim h7292 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9121 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73656 (p2352 p4594 p4597 : Prop)
    (h66348 : p4597 ∨ p4594)
    (h7315 : p2352 ∨ (¬ p4597))
    : p4594 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4594) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2352) := (fun h => hn (Or.inr h));
    let u2 : p4597 := (Or.elim h66348 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7315 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73658 (p2352 p3956 p4594 p4597 : Prop)
    (h66348 : p4597 ∨ p4594)
    (h7309 : p3956 ∨ (¬ p4594))
    (h9936 : (¬ p2352) ∨ (¬ p3956))
    : p4597 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4597) := (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4594 := (Or.elim h66348 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3956 := (Or.elim h7309 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9936 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73660 (p2363 p4600 p4602 : Prop)
    (h66349 : p4602 ∨ p4600)
    (h7332 : p2363 ∨ (¬ p4602))
    : p4600 ∨ p2363 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4600) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr h));
    let u2 : p4602 := (Or.elim h66349 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7332 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73662 (p2363 p4347 p4600 p4602 : Prop)
    (h66349 : p4602 ∨ p4600)
    (h7326 : p4347 ∨ (¬ p4600))
    (h9150 : (¬ p2363) ∨ (¬ p4347))
    : p4602 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4602) := (fun h => hn (Or.inl h));
    let u1 : p2363 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4600 := (Or.elim h66349 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4347 := (Or.elim h7326 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9150 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73664 (p2373 p4606 p4609 : Prop)
    (h66350 : p4609 ∨ p4606)
    (h7349 : p2373 ∨ (¬ p4609))
    : p4606 ∨ p2373 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4606) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2373) := (fun h => hn (Or.inr h));
    let u2 : p4609 := (Or.elim h66350 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7349 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73666 (p2373 p3880 p4606 p4609 : Prop)
    (h66350 : p4609 ∨ p4606)
    (h7343 : p3880 ∨ (¬ p4606))
    (h10253 : (¬ p2373) ∨ (¬ p3880))
    : p4609 ∨ (¬ p2373) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4609) := (fun h => hn (Or.inl h));
    let u1 : p2373 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4606 := (Or.elim h66350 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3880 := (Or.elim h7343 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10253 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73668 (p2383 p4612 p4615 : Prop)
    (h66351 : p4615 ∨ p4612)
    (h7367 : p2383 ∨ (¬ p4615))
    : p4612 ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4612) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2383) := (fun h => hn (Or.inr h));
    let u2 : p4615 := (Or.elim h66351 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7367 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73670 (p2383 p2387 p4612 p4615 : Prop)
    (h66351 : p4615 ∨ p4612)
    (h7361 : p2387 ∨ (¬ p4612))
    (h9785 : (¬ p2383) ∨ (¬ p2387))
    : p4615 ∨ (¬ p2383) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4615) := (fun h => hn (Or.inl h));
    let u1 : p2383 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4612 := (Or.elim h66351 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2387 := (Or.elim h7361 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9785 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73672 (p2396 p4619 p4622 : Prop)
    (h66352 : p4619 ∨ p4622)
    (h7384 : p2396 ∨ (¬ p4622))
    : p4619 ∨ p2396 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4619) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr h));
    let u2 : p4622 := (Or.elim h66352 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7384 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73674 (p2396 p4107 p4619 p4622 : Prop)
    (h66352 : p4619 ∨ p4622)
    (h7378 : p4107 ∨ (¬ p4619))
    (h8720 : (¬ p2396) ∨ (¬ p4107))
    : p4622 ∨ (¬ p2396) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4622) := (fun h => hn (Or.inl h));
    let u1 : p2396 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4619 := (Or.elim h66352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4107 := (Or.elim h7378 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8720 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73676 (p2406 p4627 p4630 : Prop)
    (h66353 : p4627 ∨ p4630)
    (h7401 : p2406 ∨ (¬ p4630))
    : p4627 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4627) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2406) := (fun h => hn (Or.inr h));
    let u2 : p4630 := (Or.elim h66353 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7401 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73678 (p2406 p3238 p4627 p4630 : Prop)
    (h66353 : p4627 ∨ p4630)
    (h7395 : p3238 ∨ (¬ p4627))
    (h8977 : (¬ p2406) ∨ (¬ p3238))
    : p4630 ∨ (¬ p2406) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4630) := (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4627 := (Or.elim h66353 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3238 := (Or.elim h7395 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8977 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73680 (p2417 p4634 p4639 : Prop)
    (h66354 : p4634 ∨ p4639)
    (h7418 : p2417 ∨ (¬ p4639))
    : p4634 ∨ p2417 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4634) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2417) := (fun h => hn (Or.inr h));
    let u2 : p4639 := (Or.elim h66354 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7418 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73682 (p2417 p4278 p4634 p4639 : Prop)
    (h66354 : p4634 ∨ p4639)
    (h7412 : p4278 ∨ (¬ p4634))
    (h9835 : (¬ p2417) ∨ (¬ p4278))
    : p4639 ∨ (¬ p2417) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4639) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4634 := (Or.elim h66354 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4278 := (Or.elim h7412 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9835 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73684 (p2427 p4643 p4645 : Prop)
    (h66355 : p4643 ∨ p4645)
    (h7435 : p2427 ∨ (¬ p4645))
    : p4643 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4643) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr h));
    let u2 : p4645 := (Or.elim h66355 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7435 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73686 (p2427 p4235 p4643 p4645 : Prop)
    (h66355 : p4643 ∨ p4645)
    (h7429 : p4235 ∨ (¬ p4643))
    (h9416 : (¬ p2427) ∨ (¬ p4235))
    : p4645 ∨ (¬ p2427) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4645) := (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4643 := (Or.elim h66355 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4235 := (Or.elim h7429 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9416 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73688 (p2437 p4649 p4651 : Prop)
    (h66356 : p4651 ∨ p4649)
    (h7453 : p2437 ∨ (¬ p4651))
    : p4649 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4649) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr h));
    let u2 : p4651 := (Or.elim h66356 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7453 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73690 (p2437 p3742 p4649 p4651 : Prop)
    (h66356 : p4651 ∨ p4649)
    (h7447 : p3742 ∨ (¬ p4649))
    (h9612 : (¬ p2437) ∨ (¬ p3742))
    : p4651 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4651) := (fun h => hn (Or.inl h));
    let u1 : p2437 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4649 := (Or.elim h66356 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3742 := (Or.elim h7447 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9612 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73692 (p2449 p4655 p4659 : Prop)
    (h66357 : p4655 ∨ p4659)
    (h7470 : p2449 ∨ (¬ p4659))
    : p4655 ∨ p2449 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4655) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr h));
    let u2 : p4659 := (Or.elim h66357 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7470 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73696 (p2459 p4665 p4667 : Prop)
    (h66358 : p4665 ∨ p4667)
    (h7487 : p2459 ∨ (¬ p4667))
    : p4665 ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4665) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr h));
    let u2 : p4667 := (Or.elim h66358 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7487 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73698 (p2459 p4348 p4665 p4667 : Prop)
    (h66358 : p4665 ∨ p4667)
    (h7481 : p4348 ∨ (¬ p4665))
    (h9286 : (¬ p2459) ∨ (¬ p4348))
    : p4667 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4667) := (fun h => hn (Or.inl h));
    let u1 : p2459 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4665 := (Or.elim h66358 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4348 := (Or.elim h7481 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9286 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73708 (p2528 p4692 p4694 : Prop)
    (h66366 : p4692 ∨ p4694)
    (h7573 : p2528 ∨ (¬ p4694))
    : p4692 ∨ p2528 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4692) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr h));
    let u2 : p4694 := (Or.elim h66366 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7573 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73710 (p2528 p2534 p4692 p4694 : Prop)
    (h66366 : p4692 ∨ p4694)
    (h7567 : p2534 ∨ (¬ p4692))
    (h8701 : (¬ p2528) ∨ (¬ p2534))
    : p4694 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4694) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4692 := (Or.elim h66366 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2534 := (Or.elim h7567 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8701 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73712 (p2440 p2542 p4699 p4703 : Prop)
    (h66367 : p4703 ∨ p4699)
    (h7590 : p2542 ∨ (¬ p4703))
    (h9451 : (¬ p2440) ∨ (¬ p2542))
    : p4699 ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4699) := (fun h => hn (Or.inl h));
    let u1 : p2440 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4703 := (Or.elim h66367 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p2542 := (Or.elim h7590 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9451 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73714 (p2440 p4699 p4703 : Prop)
    (h66367 : p4703 ∨ p4699)
    (h7584 : p2440 ∨ (¬ p4699))
    : p4703 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4703) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : p4699 := (Or.elim h66367 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7584 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73716 (p2553 p4707 p4709 : Prop)
    (h66368 : p4709 ∨ p4707)
    (h7607 : p2553 ∨ (¬ p4709))
    : p4707 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4707) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr h));
    let u2 : p4709 := (Or.elim h66368 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7607 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73718 (p2553 p2588 p4707 p4709 : Prop)
    (h66368 : p4709 ∨ p4707)
    (h7601 : p2588 ∨ (¬ p4707))
    (h9753 : (¬ p2553) ∨ (¬ p2588))
    : p4709 ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4709) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4707 := (Or.elim h66368 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2588 := (Or.elim h7601 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9753 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73720 (p2563 p4714 p4716 : Prop)
    (h66369 : p4714 ∨ p4716)
    (h7624 : p2563 ∨ (¬ p4716))
    : p4714 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4714) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr h));
    let u2 : p4716 := (Or.elim h66369 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7624 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73722 (p2563 p4110 p4714 p4716 : Prop)
    (h66369 : p4714 ∨ p4716)
    (h7618 : p4110 ∨ (¬ p4714))
    (h9440 : (¬ p2563) ∨ (¬ p4110))
    : p4716 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4716) := (fun h => hn (Or.inl h));
    let u1 : p2563 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4714 := (Or.elim h66369 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4110 := (Or.elim h7618 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9440 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73728 (p2598 p4726 p4728 : Prop)
    (h66373 : p4728 ∨ p4726)
    (h7670 : p2598 ∨ (¬ p4728))
    : p4726 ∨ p2598 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4726) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2598) := (fun h => hn (Or.inr h));
    let u2 : p4728 := (Or.elim h66373 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7670 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73730 (p2598 p3055 p4726 p4728 : Prop)
    (h66373 : p4728 ∨ p4726)
    (h7664 : p3055 ∨ (¬ p4726))
    (h9095 : (¬ p2598) ∨ (¬ p3055))
    : p4728 ∨ (¬ p2598) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4728) := (fun h => hn (Or.inl h));
    let u1 : p2598 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4726 := (Or.elim h66373 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3055 := (Or.elim h7664 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9095 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73732 (p2608 p4732 p4735 : Prop)
    (h66374 : p4732 ∨ p4735)
    (h7687 : p2608 ∨ (¬ p4735))
    : p4732 ∨ p2608 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4732) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2608) := (fun h => hn (Or.inr h));
    let u2 : p4735 := (Or.elim h66374 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7687 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73734 (p2608 p3954 p4732 p4735 : Prop)
    (h66374 : p4732 ∨ p4735)
    (h7681 : p3954 ∨ (¬ p4732))
    (h9054 : (¬ p2608) ∨ (¬ p3954))
    : p4735 ∨ (¬ p2608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4735) := (fun h => hn (Or.inl h));
    let u1 : p2608 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4732 := (Or.elim h66374 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3954 := (Or.elim h7681 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9054 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73738 (p2619 p3694 p4739 p4743 : Prop)
    (h66375 : p4739 ∨ p4743)
    (h7698 : p3694 ∨ (¬ p4739))
    (h9933 : (¬ p2619) ∨ (¬ p3694))
    : p4743 ∨ (¬ p2619) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4743) := (fun h => hn (Or.inl h));
    let u1 : p2619 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4739 := (Or.elim h66375 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3694 := (Or.elim h7698 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9933 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73740 (p2630 p4748 p4751 : Prop)
    (h66376 : p4751 ∨ p4748)
    (h7721 : p2630 ∨ (¬ p4751))
    : p4748 ∨ p2630 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4748) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2630) := (fun h => hn (Or.inr h));
    let u2 : p4751 := (Or.elim h66376 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7721 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73742 (p2630 p2810 p4748 p4751 : Prop)
    (h66376 : p4751 ∨ p4748)
    (h7715 : p2810 ∨ (¬ p4748))
    (h9606 : (¬ p2630) ∨ (¬ p2810))
    : p4751 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4751) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4748 := (Or.elim h66376 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p2810 := (Or.elim h7715 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9606 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73744 (p2641 p4755 p4758 : Prop)
    (h66377 : p4758 ∨ p4755)
    (h7739 : p2641 ∨ (¬ p4758))
    : p4755 ∨ p2641 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4755) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2641) := (fun h => hn (Or.inr h));
    let u2 : p4758 := (Or.elim h66377 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7739 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73746 (p2641 p4154 p4755 p4758 : Prop)
    (h66377 : p4758 ∨ p4755)
    (h7733 : p4154 ∨ (¬ p4755))
    (h10070 : (¬ p2641) ∨ (¬ p4154))
    : p4758 ∨ (¬ p2641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4758) := (fun h => hn (Or.inl h));
    let u1 : p2641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4755 := (Or.elim h66377 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4154 := (Or.elim h7733 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10070 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73750 (p2668 p4768 p4772 : Prop)
    (h66381 : p4772 ∨ p4768)
    (h7777 : p2668 ∨ (¬ p4772))
    : p4768 ∨ p2668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4768) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2668) := (fun h => hn (Or.inr h));
    let u2 : p4772 := (Or.elim h66381 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7777 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73752 (p2668 p3324 p4768 p4772 : Prop)
    (h66381 : p4772 ∨ p4768)
    (h7771 : p3324 ∨ (¬ p4768))
    (h9896 : (¬ p2668) ∨ (¬ p3324))
    : p4772 ∨ (¬ p2668) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4772) := (fun h => hn (Or.inl h));
    let u1 : p2668 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4768 := (Or.elim h66381 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3324 := (Or.elim h7771 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9896 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73756 (p2685 p3572 p4776 p4780 : Prop)
    (h66382 : p4776 ∨ p4780)
    (h7788 : p3572 ∨ (¬ p4776))
    (h11420 : (¬ p2685) ∨ (¬ p3572))
    : p4780 ∨ (¬ p2685) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4780) := (fun h => hn (Or.inl h));
    let u1 : p2685 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4776 := (Or.elim h66382 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3572 := (Or.elim h7788 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h11420 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73758 (p2696 p4785 p4788 : Prop)
    (h66383 : p4785 ∨ p4788)
    (h7811 : p2696 ∨ (¬ p4788))
    : p4785 ∨ p2696 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4785) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2696) := (fun h => hn (Or.inr h));
    let u2 : p4788 := (Or.elim h66383 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7811 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73760 (p2696 p3365 p4785 p4788 : Prop)
    (h66383 : p4785 ∨ p4788)
    (h7805 : p3365 ∨ (¬ p4785))
    (h9080 : (¬ p2696) ∨ (¬ p3365))
    : p4788 ∨ (¬ p2696) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4788) := (fun h => hn (Or.inl h));
    let u1 : p2696 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4785 := (Or.elim h66383 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3365 := (Or.elim h7805 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9080 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73762 (p2707 p4792 p4795 : Prop)
    (h66384 : p4792 ∨ p4795)
    (h7829 : p2707 ∨ (¬ p4795))
    : p4792 ∨ p2707 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4792) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2707) := (fun h => hn (Or.inr h));
    let u2 : p4795 := (Or.elim h66384 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7829 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73764 (p2707 p3588 p4792 p4795 : Prop)
    (h66384 : p4792 ∨ p4795)
    (h7823 : p3588 ∨ (¬ p4792))
    (h9154 : (¬ p2707) ∨ (¬ p3588))
    : p4795 ∨ (¬ p2707) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4795) := (fun h => hn (Or.inl h));
    let u1 : p2707 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4792 := (Or.elim h66384 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3588 := (Or.elim h7823 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9154 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73766 (p2717 p4799 p4803 : Prop)
    (h66385 : p4803 ∨ p4799)
    (h7846 : p2717 ∨ (¬ p4803))
    : p4799 ∨ p2717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4799) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2717) := (fun h => hn (Or.inr h));
    let u2 : p4803 := (Or.elim h66385 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7846 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73770 (p2727 p4809 p4812 : Prop)
    (h66386 : p4809 ∨ p4812)
    (h7863 : p2727 ∨ (¬ p4812))
    : p4809 ∨ p2727 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4809) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2727) := (fun h => hn (Or.inr h));
    let u2 : p4812 := (Or.elim h66386 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h7863 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73772 (p2727 p4111 p4809 p4812 : Prop)
    (h66386 : p4809 ∨ p4812)
    (h7857 : p4111 ∨ (¬ p4809))
    (h7872 : (¬ p2727) ∨ (¬ p4111))
    : p4812 ∨ (¬ p2727) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4812) := (fun h => hn (Or.inl h));
    let u1 : p2727 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4809 := (Or.elim h66386 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4111 := (Or.elim h7857 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h7872 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73778 (p2761 p4822 p4827 : Prop)
    (h66390 : p4827 ∨ p4822)
    (h7908 : p2761 ∨ (¬ p4827))
    : p4822 ∨ p2761 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4822) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr h));
    let u2 : p4827 := (Or.elim h66390 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7908 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73780 (p2761 p4381 p4822 p4827 : Prop)
    (h66390 : p4827 ∨ p4822)
    (h7902 : p4381 ∨ (¬ p4822))
    (h10478 : (¬ p2761) ∨ (¬ p4381))
    : p4827 ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4827) := (fun h => hn (Or.inl h));
    let u1 : p2761 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4822 := (Or.elim h66390 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4381 := (Or.elim h7902 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10478 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73786 (p2797 p4840 p4844 : Prop)
    (h66394 : p4844 ∨ p4840)
    (h7953 : p2797 ∨ (¬ p4844))
    : p4840 ∨ p2797 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4840) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr h));
    let u2 : p4844 := (Or.elim h66394 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7953 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73788 (p2797 p4195 p4840 p4844 : Prop)
    (h66394 : p4844 ∨ p4840)
    (h7947 : p4195 ∨ (¬ p4840))
    (h10905 : (¬ p2797) ∨ (¬ p4195))
    : p4844 ∨ (¬ p2797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4844) := (fun h => hn (Or.inl h));
    let u1 : p2797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4840 := (Or.elim h66394 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4195 := (Or.elim h7947 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10905 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73792 (p2807 p3414 p4848 p4852 : Prop)
    (h67247 : p4848 ∨ p4852)
    (h7965 : p3414 ∨ (¬ p4848))
    (h9096 : (¬ p2807) ∨ (¬ p3414))
    : p4852 ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4852) := (fun h => hn (Or.inl h));
    let u1 : p2807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4848 := (Or.elim h67247 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3414 := (Or.elim h7965 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9096 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73796 (p2819 p4358 p4856 p4860 : Prop)
    (h66395 : p4856 ∨ p4860)
    (h7983 : p4358 ∨ (¬ p4856))
    (h10948 : (¬ p2819) ∨ (¬ p4358))
    : p4860 ∨ (¬ p2819) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4860) := (fun h => hn (Or.inl h));
    let u1 : p2819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4856 := (Or.elim h66395 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4358 := (Or.elim h7983 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10948 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73798 (p2829 p4865 p4868 : Prop)
    (h66396 : p4865 ∨ p4868)
    (h8006 : p2829 ∨ (¬ p4868))
    : p4865 ∨ p2829 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4865) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2829) := (fun h => hn (Or.inr h));
    let u2 : p4868 := (Or.elim h66396 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8006 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73800 (p2829 p3688 p4865 p4868 : Prop)
    (h66396 : p4865 ∨ p4868)
    (h8000 : p3688 ∨ (¬ p4865))
    (h10789 : (¬ p2829) ∨ (¬ p3688))
    : p4868 ∨ (¬ p2829) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4868) := (fun h => hn (Or.inl h));
    let u1 : p2829 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4865 := (Or.elim h66396 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3688 := (Or.elim h8000 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10789 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73802 (p2839 p4873 p4876 : Prop)
    (h66397 : p4873 ∨ p4876)
    (h8023 : p2839 ∨ (¬ p4876))
    : p4873 ∨ p2839 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4873) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2839) := (fun h => hn (Or.inr h));
    let u2 : p4876 := (Or.elim h66397 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8023 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73804 (p2839 p3583 p4873 p4876 : Prop)
    (h66397 : p4873 ∨ p4876)
    (h8017 : p3583 ∨ (¬ p4873))
    (h9144 : (¬ p2839) ∨ (¬ p3583))
    : p4876 ∨ (¬ p2839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4876) := (fun h => hn (Or.inl h));
    let u1 : p2839 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4873 := (Or.elim h66397 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3583 := (Or.elim h8017 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9144 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73806 (p2850 p4880 p4883 : Prop)
    (h66398 : p4880 ∨ p4883)
    (h8040 : p2850 ∨ (¬ p4883))
    : p4880 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4880) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2850) := (fun h => hn (Or.inr h));
    let u2 : p4883 := (Or.elim h66398 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8040 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73808 (p2850 p3684 p4880 p4883 : Prop)
    (h66398 : p4880 ∨ p4883)
    (h8034 : p3684 ∨ (¬ p4880))
    (h9415 : (¬ p2850) ∨ (¬ p3684))
    : p4883 ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4883) := (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4880 := (Or.elim h66398 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3684 := (Or.elim h8034 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9415 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73810 (p2860 p4887 p4890 : Prop)
    (h66399 : p4887 ∨ p4890)
    (h8057 : p2860 ∨ (¬ p4890))
    : p4887 ∨ p2860 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4887) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2860) := (fun h => hn (Or.inr h));
    let u2 : p4890 := (Or.elim h66399 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8057 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73812 (p2860 p3758 p4887 p4890 : Prop)
    (h66399 : p4887 ∨ p4890)
    (h8051 : p3758 ∨ (¬ p4887))
    (h10610 : (¬ p2860) ∨ (¬ p3758))
    : p4890 ∨ (¬ p2860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4890) := (fun h => hn (Or.inl h));
    let u1 : p2860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4887 := (Or.elim h66399 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3758 := (Or.elim h8051 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10610 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73814 (p2870 p4893 p4896 : Prop)
    (h66400 : p4896 ∨ p4893)
    (h8074 : p2870 ∨ (¬ p4896))
    : p4893 ∨ p2870 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4893) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2870) := (fun h => hn (Or.inr h));
    let u2 : p4896 := (Or.elim h66400 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8074 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73816 (p2870 p4244 p4893 p4896 : Prop)
    (h66400 : p4896 ∨ p4893)
    (h8068 : p4244 ∨ (¬ p4893))
    (h9153 : (¬ p2870) ∨ (¬ p4244))
    : p4896 ∨ (¬ p2870) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4896) := (fun h => hn (Or.inl h));
    let u1 : p2870 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4893 := (Or.elim h66400 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4244 := (Or.elim h8068 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9153 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73818 (p2881 p4900 p4903 : Prop)
    (h66401 : p4903 ∨ p4900)
    (h8092 : p2881 ∨ (¬ p4903))
    : p4900 ∨ p2881 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4900) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr h));
    let u2 : p4903 := (Or.elim h66401 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8092 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73820 (p2881 p3570 p4900 p4903 : Prop)
    (h66401 : p4903 ∨ p4900)
    (h8086 : p3570 ∨ (¬ p4900))
    (h9899 : (¬ p2881) ∨ (¬ p3570))
    : p4903 ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4903) := (fun h => hn (Or.inl h));
    let u1 : p2881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4900 := (Or.elim h66401 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3570 := (Or.elim h8086 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9899 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73822 (p2891 p4908 p4912 : Prop)
    (h66402 : p4912 ∨ p4908)
    (h8110 : p2891 ∨ (¬ p4912))
    : p4908 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4908) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2891) := (fun h => hn (Or.inr h));
    let u2 : p4912 := (Or.elim h66402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8110 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73824 (p2891 p3486 p4908 p4912 : Prop)
    (h66402 : p4912 ∨ p4908)
    (h8104 : p3486 ∨ (¬ p4908))
    (h10093 : (¬ p2891) ∨ (¬ p3486))
    : p4912 ∨ (¬ p2891) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4912) := (fun h => hn (Or.inl h));
    let u1 : p2891 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4908 := (Or.elim h66402 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3486 := (Or.elim h8104 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10093 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73826 (p2901 p4916 p4918 : Prop)
    (h66403 : p4916 ∨ p4918)
    (h8127 : p2901 ∨ (¬ p4918))
    : p4916 ∨ p2901 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4916) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2901) := (fun h => hn (Or.inr h));
    let u2 : p4918 := (Or.elim h66403 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8127 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73828 (p2901 p4320 p4916 p4918 : Prop)
    (h66403 : p4916 ∨ p4918)
    (h8121 : p4320 ∨ (¬ p4916))
    (h9331 : (¬ p2901) ∨ (¬ p4320))
    : p4918 ∨ (¬ p2901) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4918) := (fun h => hn (Or.inl h));
    let u1 : p2901 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4916 := (Or.elim h66403 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4320 := (Or.elim h8121 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9331 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73830 (p2911 p4921 p4923 : Prop)
    (h66404 : p4923 ∨ p4921)
    (h8144 : p2911 ∨ (¬ p4923))
    : p4921 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4921) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2911) := (fun h => hn (Or.inr h));
    let u2 : p4923 := (Or.elim h66404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8144 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73832 (p2911 p3644 p4921 p4923 : Prop)
    (h66404 : p4923 ∨ p4921)
    (h8138 : p3644 ∨ (¬ p4921))
    (h9125 : (¬ p2911) ∨ (¬ p3644))
    : p4923 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4923) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4921 := (Or.elim h66404 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3644 := (Or.elim h8138 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9125 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73844 (p2982 p4946 p4951 : Prop)
    (h66412 : p4946 ∨ p4951)
    (h8229 : p2982 ∨ (¬ p4951))
    : p4946 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4946) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr h));
    let u2 : p4951 := (Or.elim h66412 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8229 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73845 (p2982 p4948 : Prop)
    (h11585 : (¬ p2982) ∨ (¬ p4948))
    : (¬ p2982) ∨ (¬ p4948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4948 := Classical.byContradiction (fun h => hn (Or.inr h));
    (Or.elim h11585 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u1)))))

theorem step73846 (p2982 p4948 p5956 p5957 : Prop)
    (h12720 : p4948 ∨ p5956)
    (h66559 : (¬ p5956) ∨ (¬ p5957))
    (h12727 : p2982 ∨ p5957)
    : p4948 ∨ p2982 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4948) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2982) := (fun h => hn (Or.inr h));
    let u2 : p5956 := (Or.elim h12720 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p5957) := (Or.elim h66559 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h12727 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step73848 (p2982 p4946 p4948 p4951 : Prop)
    (h66412 : p4946 ∨ p4951)
    (h8223 : (¬ p4946) ∨ p4948)
    (h11585 : (¬ p2982) ∨ (¬ p4948))
    : p4951 ∨ (¬ p2982) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4951) := (fun h => hn (Or.inl h));
    let u1 : p2982 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4946 := (Or.elim h66412 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4948 := (Or.elim h8223 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h11585 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73850 (p2992 p4956 p4958 : Prop)
    (h66413 : p4956 ∨ p4958)
    (h8246 : p2992 ∨ (¬ p4958))
    : p4956 ∨ p2992 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4956) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2992) := (fun h => hn (Or.inr h));
    let u2 : p4958 := (Or.elim h66413 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8246 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73852 (p2992 p3662 p4956 p4958 : Prop)
    (h66413 : p4956 ∨ p4958)
    (h8240 : p3662 ∨ (¬ p4956))
    (h8869 : (¬ p2992) ∨ (¬ p3662))
    : p4958 ∨ (¬ p2992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4958) := (fun h => hn (Or.inl h));
    let u1 : p2992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4956 := (Or.elim h66413 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3662 := (Or.elim h8240 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8869 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73858 (p3016 p4971 p4974 : Prop)
    (h66415 : p4974 ∨ p4971)
    (h8280 : p3016 ∨ (¬ p4974))
    : p4971 ∨ p3016 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4971) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr h));
    let u2 : p4974 := (Or.elim h66415 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8280 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73860 (p3016 p3574 p4971 p4974 : Prop)
    (h66415 : p4974 ∨ p4971)
    (h8274 : p3574 ∨ (¬ p4971))
    (h10212 : (¬ p3016) ∨ (¬ p3574))
    : p4974 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4974) := (fun h => hn (Or.inl h));
    let u1 : p3016 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4971 := (Or.elim h66415 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3574 := (Or.elim h8274 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10212 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73866 (p3051 p3556 p4983 p4987 : Prop)
    (h66419 : p4983 ∨ p4987)
    (h8315 : p3556 ∨ (¬ p4983))
    (h9152 : (¬ p3051) ∨ (¬ p3556))
    : p4987 ∨ (¬ p3051) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4987) := (fun h => hn (Or.inl h));
    let u1 : p3051 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4983 := (Or.elim h66419 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3556 := (Or.elim h8315 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9152 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73868 (p3073 p5000 p5003 : Prop)
    (h66421 : p5003 ∨ p5000)
    (h8357 : p3073 ∨ (¬ p5003))
    : p5000 ∨ p3073 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5000) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3073) := (fun h => hn (Or.inr h));
    let u2 : p5003 := (Or.elim h66421 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8357 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73872 (p3083 p5007 p5010 : Prop)
    (h66422 : p5007 ∨ p5010)
    (h8375 : p3083 ∨ (¬ p5010))
    : p5007 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5007) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr h));
    let u2 : p5010 := (Or.elim h66422 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8375 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73874 (p3083 p4256 p5007 p5010 : Prop)
    (h66422 : p5007 ∨ p5010)
    (h8369 : p4256 ∨ (¬ p5007))
    (h10987 : (¬ p3083) ∨ (¬ p4256))
    : p5010 ∨ (¬ p3083) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5010) := (fun h => hn (Or.inl h));
    let u1 : p3083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5007 := (Or.elim h66422 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4256 := (Or.elim h8369 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10987 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73876 (p3093 p5014 p5019 : Prop)
    (h66423 : p5019 ∨ p5014)
    (h8392 : p3093 ∨ (¬ p5019))
    : p5014 ∨ p3093 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5014) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3093) := (fun h => hn (Or.inr h));
    let u2 : p5019 := (Or.elim h66423 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8392 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73878 (p3093 p3591 p5014 p5019 : Prop)
    (h66423 : p5019 ∨ p5014)
    (h8386 : p3591 ∨ (¬ p5014))
    (h8401 : (¬ p3093) ∨ (¬ p3591))
    : p5019 ∨ (¬ p3093) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5019) := (fun h => hn (Or.inl h));
    let u1 : p3093 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5014 := (Or.elim h66423 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3591 := (Or.elim h8386 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8401 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73888 (p3125 p5042 p5044 : Prop)
    (h66426 : p5042 ∨ p5044)
    (h8445 : p3125 ∨ (¬ p5044))
    : p5042 ∨ p3125 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5042) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr h));
    let u2 : p5044 := (Or.elim h66426 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8445 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73890 (p3125 p3744 p5042 p5044 : Prop)
    (h66426 : p5042 ∨ p5044)
    (h8439 : p3744 ∨ (¬ p5042))
    (h9853 : (¬ p3125) ∨ (¬ p3744))
    : p5044 ∨ (¬ p3125) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5044) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5042 := (Or.elim h66426 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3744 := (Or.elim h8439 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9853 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73892 (p3136 p5048 p5050 : Prop)
    (h66427 : p5048 ∨ p5050)
    (h8462 : p3136 ∨ (¬ p5050))
    : p5048 ∨ p3136 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5048) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3136) := (fun h => hn (Or.inr h));
    let u2 : p5050 := (Or.elim h66427 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8462 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73894 (p3136 p4315 p5048 p5050 : Prop)
    (h66427 : p5048 ∨ p5050)
    (h8456 : p4315 ∨ (¬ p5048))
    (h10894 : (¬ p3136) ∨ (¬ p4315))
    : p5050 ∨ (¬ p3136) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5050) := (fun h => hn (Or.inl h));
    let u1 : p3136 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5048 := (Or.elim h66427 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4315 := (Or.elim h8456 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10894 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73896 (p3146 p5055 p5057 : Prop)
    (h66428 : p5055 ∨ p5057)
    (h8479 : p3146 ∨ (¬ p5057))
    : p5055 ∨ p3146 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5055) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3146) := (fun h => hn (Or.inr h));
    let u2 : p5057 := (Or.elim h66428 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8479 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73898 (p3146 p3692 p5055 p5057 : Prop)
    (h66428 : p5055 ∨ p5057)
    (h8473 : p3692 ∨ (¬ p5055))
    (h9906 : (¬ p3146) ∨ (¬ p3692))
    : p5057 ∨ (¬ p3146) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5057) := (fun h => hn (Or.inl h));
    let u1 : p3146 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5055 := (Or.elim h66428 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3692 := (Or.elim h8473 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9906 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73900 (p3156 p5061 p5064 : Prop)
    (h66429 : p5061 ∨ p5064)
    (h8496 : p3156 ∨ (¬ p5064))
    : p5061 ∨ p3156 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5061) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3156) := (fun h => hn (Or.inr h));
    let u2 : p5064 := (Or.elim h66429 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8496 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73902 (p3156 p3497 p5061 p5064 : Prop)
    (h66429 : p5061 ∨ p5064)
    (h8490 : p3497 ∨ (¬ p5061))
    (h9439 : (¬ p3156) ∨ (¬ p3497))
    : p5064 ∨ (¬ p3156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5064) := (fun h => hn (Or.inl h));
    let u1 : p3156 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5061 := (Or.elim h66429 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3497 := (Or.elim h8490 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9439 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73910 (p3189 p4360 p5073 p5077 : Prop)
    (h66430 : p5073 ∨ p5077)
    (h8534 : p4360 ∨ (¬ p5073))
    (h10114 : (¬ p3189) ∨ (¬ p4360))
    : p5077 ∨ (¬ p3189) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5077) := (fun h => hn (Or.inl h));
    let u1 : p3189 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5073 := (Or.elim h66430 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4360 := (Or.elim h8534 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10114 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73912 (p3201 p5081 p5084 : Prop)
    (h66431 : p5081 ∨ p5084)
    (h8558 : p3201 ∨ (¬ p5084))
    : p5081 ∨ p3201 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5081) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3201) := (fun h => hn (Or.inr h));
    let u2 : p5084 := (Or.elim h66431 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8558 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73918 (p3246 p5101 p5103 : Prop)
    (h66436 : p5101 ∨ p5103)
    (h8615 : p3246 ∨ (¬ p5103))
    : p5101 ∨ p3246 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5101) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3246) := (fun h => hn (Or.inr h));
    let u2 : p5103 := (Or.elim h66436 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8615 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73920 (p3246 p3690 p5101 p5103 : Prop)
    (h66436 : p5101 ∨ p5103)
    (h8609 : p3690 ∨ (¬ p5101))
    (h10589 : (¬ p3246) ∨ (¬ p3690))
    : p5103 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5103) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5101 := (Or.elim h66436 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3690 := (Or.elim h8609 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10589 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73922 (p3256 p5106 p5110 : Prop)
    (h66437 : p5106 ∨ p5110)
    (h8634 : p3256 ∨ (¬ p5110))
    : p5106 ∨ p3256 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5106) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3256) := (fun h => hn (Or.inr h));
    let u2 : p5110 := (Or.elim h66437 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8634 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73924 (p3256 p4118 p5106 p5110 : Prop)
    (h66437 : p5106 ∨ p5110)
    (h8628 : p4118 ∨ (¬ p5106))
    (h10930 : (¬ p3256) ∨ (¬ p4118))
    : p5110 ∨ (¬ p3256) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5110) := (fun h => hn (Or.inl h));
    let u1 : p3256 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5106 := (Or.elim h66437 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4118 := (Or.elim h8628 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10930 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73926 (p3266 p5115 p5120 : Prop)
    (h66438 : p5115 ∨ p5120)
    (h8652 : p3266 ∨ (¬ p5120))
    : p5115 ∨ p3266 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5115) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3266) := (fun h => hn (Or.inr h));
    let u2 : p5120 := (Or.elim h66438 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8652 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73928 (p3266 p4444 p5115 p5120 : Prop)
    (h66438 : p5115 ∨ p5120)
    (h8646 : p4444 ∨ (¬ p5115))
    (h11336 : (¬ p3266) ∨ (¬ p4444))
    : p5120 ∨ (¬ p3266) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5120) := (fun h => hn (Or.inl h));
    let u1 : p3266 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5115 := (Or.elim h66438 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4444 := (Or.elim h8646 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h11336 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73936 (p3309 p5140 p5143 : Prop)
    (h66440 : p5140 ∨ p5143)
    (h8711 : p3309 ∨ (¬ p5143))
    : p5140 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5140) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr h));
    let u2 : p5143 := (Or.elim h66440 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8711 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73938 (p3309 p3549 p5140 p5143 : Prop)
    (h66440 : p5140 ∨ p5143)
    (h8705 : p3549 ∨ (¬ p5140))
    (h9922 : (¬ p3309) ∨ (¬ p3549))
    : p5143 ∨ (¬ p3309) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5143) := (fun h => hn (Or.inl h));
    let u1 : p3309 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5140 := (Or.elim h66440 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3549 := (Or.elim h8705 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9922 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73946 (p3343 p3359 p5169 p5174 : Prop)
    (h66443 : p5169 ∨ p5174)
    (h8759 : p3359 ∨ (¬ p5169))
    (h11519 : (¬ p3343) ∨ (¬ p3359))
    : p5174 ∨ (¬ p3343) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5174) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5169 := (Or.elim h66443 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3359 := (Or.elim h8759 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h11519 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73948 (p3379 p5189 p5192 : Prop)
    (h66445 : p5189 ∨ p5192)
    (h8805 : p3379 ∨ (¬ p5192))
    : p5189 ∨ p3379 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5189) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3379) := (fun h => hn (Or.inr h));
    let u2 : p5192 := (Or.elim h66445 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8805 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73950 (p3379 p3452 p5189 p5192 : Prop)
    (h66445 : p5189 ∨ p5192)
    (h8799 : p3452 ∨ (¬ p5189))
    (h10069 : (¬ p3379) ∨ (¬ p3452))
    : p5192 ∨ (¬ p3379) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5192) := (fun h => hn (Or.inl h));
    let u1 : p3379 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5189 := (Or.elim h66445 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3452 := (Or.elim h8799 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10069 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73952 (p3389 p5196 p5200 : Prop)
    (h66446 : p5196 ∨ p5200)
    (h8822 : p3389 ∨ (¬ p5200))
    : p5196 ∨ p3389 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5196) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr h));
    let u2 : p5200 := (Or.elim h66446 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8822 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73954 (p3389 p3540 p5196 p5200 : Prop)
    (h66446 : p5196 ∨ p5200)
    (h8816 : p3540 ∨ (¬ p5196))
    (h9914 : (¬ p3389) ∨ (¬ p3540))
    : p5200 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5200) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5196 := (Or.elim h66446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3540 := (Or.elim h8816 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9914 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73956 (p3399 p5205 p5209 : Prop)
    (h66447 : p5209 ∨ p5205)
    (h8839 : p3399 ∨ (¬ p5209))
    : p5205 ∨ p3399 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5205) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3399) := (fun h => hn (Or.inr h));
    let u2 : p5209 := (Or.elim h66447 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8839 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73958 (p3399 p4366 p5205 p5209 : Prop)
    (h66447 : p5209 ∨ p5205)
    (h8833 : p4366 ∨ (¬ p5205))
    (h9740 : (¬ p3399) ∨ (¬ p4366))
    : p5209 ∨ (¬ p3399) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5209) := (fun h => hn (Or.inl h));
    let u1 : p3399 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5205 := (Or.elim h66447 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p4366 := (Or.elim h8833 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9740 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73960 (p3367 p5213 p5215 : Prop)
    (h66448 : p5215 ∨ p5213)
    (h8859 : p3367 ∨ (¬ p5215))
    : p5213 ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5213) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3367) := (fun h => hn (Or.inr h));
    let u2 : p5215 := (Or.elim h66448 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h8859 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73962 (p3367 p3585 p5213 p5215 : Prop)
    (h66448 : p5215 ∨ p5213)
    (h8853 : p3585 ∨ (¬ p5213))
    (h8999 : (¬ p3367) ∨ (¬ p3585))
    : p5215 ∨ (¬ p3367) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5215) := (fun h => hn (Or.inl h));
    let u1 : p3367 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5213 := (Or.elim h66448 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : p3585 := (Or.elim h8853 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h8999 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73964 (p3422 p5219 p5223 : Prop)
    (h66449 : p5219 ∨ p5223)
    (h8879 : p3422 ∨ (¬ p5223))
    : p5219 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5219) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3422) := (fun h => hn (Or.inr h));
    let u2 : p5223 := (Or.elim h66449 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8879 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73966 (p3422 p3584 p5219 p5223 : Prop)
    (h66449 : p5219 ∨ p5223)
    (h8873 : p3584 ∨ (¬ p5219))
    (h9445 : (¬ p3422) ∨ (¬ p3584))
    : p5223 ∨ (¬ p3422) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5223) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5219 := (Or.elim h66449 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3584 := (Or.elim h8873 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9445 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73976 (p3461 p5246 p5251 : Prop)
    (h66452 : p5246 ∨ p5251)
    (h8934 : p3461 ∨ (¬ p5251))
    : p5246 ∨ p3461 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5246) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3461) := (fun h => hn (Or.inr h));
    let u2 : p5251 := (Or.elim h66452 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8934 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73980 (p3425 p3471 p5256 p5259 : Prop)
    (h66453 : p5259 ∨ p5256)
    (h8951 : p3471 ∨ (¬ p5259))
    (h9613 : (¬ p3425) ∨ (¬ p3471))
    : p5256 ∨ (¬ p3425) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5256) := (fun h => hn (Or.inl h));
    let u1 : p3425 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5259 := (Or.elim h66453 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3471 := (Or.elim h8951 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9613 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73982 (p3425 p5256 p5259 : Prop)
    (h66453 : p5259 ∨ p5256)
    (h8945 : p3425 ∨ (¬ p5256))
    : p5259 ∨ p3425 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5259) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3425) := (fun h => hn (Or.inr h));
    let u2 : p5256 := (Or.elim h66453 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8945 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73984 (p3323 p5273 p5277 : Prop)
    (h66455 : p5273 ∨ p5277)
    (h8987 : p3323 ∨ (¬ p5277))
    : p5273 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5273) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr h));
    let u2 : p5277 := (Or.elim h66455 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h8987 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73986 (p3323 p4037 p5273 p5277 : Prop)
    (h66455 : p5273 ∨ p5277)
    (h8981 : p4037 ∨ (¬ p5273))
    (h9699 : (¬ p3323) ∨ (¬ p4037))
    : p5277 ∨ (¬ p3323) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5277) := (fun h => hn (Or.inl h));
    let u1 : p3323 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5273 := (Or.elim h66455 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p4037 := (Or.elim h8981 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9699 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step73992 (p3527 p5304 p5306 : Prop)
    (h66458 : p5304 ∨ p5306)
    (h9044 : p3527 ∨ (¬ p5306))
    : p5304 ∨ p3527 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5304) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3527) := (fun h => hn (Or.inr h));
    let u2 : p5306 := (Or.elim h66458 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h9044 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step73994 (p3527 p3548 p5304 p5306 : Prop)
    (h66458 : p5304 ∨ p5306)
    (h9038 : p3548 ∨ (¬ p5304))
    (h9053 : (¬ p3527) ∨ (¬ p3548))
    : p5306 ∨ (¬ p3527) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5306) := (fun h => hn (Or.inl h));
    let u1 : p3527 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5304 := (Or.elim h66458 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3548 := (Or.elim h9038 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9053 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step74004 (p3599 p5327 p5331 : Prop)
    (h66461 : p5327 ∨ p5331)
    (h9164 : p3599 ∨ (¬ p5331))
    : p5327 ∨ p3599 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5327) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3599) := (fun h => hn (Or.inr h));
    let u2 : p5331 := (Or.elim h66461 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    (Or.elim h9164 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step74014 (p3631 p3817 p5356 p5361 : Prop)
    (h66464 : p5356 ∨ p5361)
    (h9211 : p3817 ∨ (¬ p5356))
    (h10493 : (¬ p3631) ∨ (¬ p3817))
    : p5361 ∨ (¬ p3631) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5361) := (fun h => hn (Or.inl h));
    let u1 : p3631 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5356 := (Or.elim h66464 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3817 := (Or.elim h9211 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h10493 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step74018 (p3641 p3874 p5367 p5372 : Prop)
    (h66465 : p5367 ∨ p5372)
    (h9235 : p3874 ∨ (¬ p5367))
    (h11620 : (¬ p3641) ∨ (¬ p3874))
    : p5372 ∨ (¬ p3641) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5372) := (fun h => hn (Or.inl h));
    let u1 : p3641 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5367 := (Or.elim h66465 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3874 := (Or.elim h9235 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h11620 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step74022 (p3654 p3946 p5377 p5382 : Prop)
    (h66466 : p5377 ∨ p5382)
    (h9255 : p3946 ∨ (¬ p5377))
    (h9737 : (¬ p3654) ∨ (¬ p3946))
    : p5382 ∨ (¬ p3654) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5382) := (fun h => hn (Or.inl h));
    let u1 : p3654 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p5377 := (Or.elim h66466 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u3 : p3946 := (Or.elim h9255 (fun q0 => q0) (fun r0 => (False.elim (r0 u2))));
    (Or.elim h9737 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (r0 u3)))))

theorem step74025 (p3670 p5387 : Prop)
    (h11268 : (¬ p3670) ∨ (¬ p5387))
    : (¬ p3670) ∨ (¬ p5387) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5387 := Classical.byContradiction (fun h => hn (Or.inr h));
    (Or.elim h11268 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u1)))))

theorem step74026 (p3670 p5387 p6103 p6104 : Prop)
    (h13765 : p5387 ∨ p6103)
    (h66608 : (¬ p6103) ∨ (¬ p6104))
    (h13772 : p3670 ∨ p6104)
    : p5387 ∨ p3670 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5387) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3670) := (fun h => hn (Or.inr h));
    let u2 : p6103 := (Or.elim h13765 (fun q0 => (False.elim (u0 q0))) (fun r0 => r0));
    let u3 : (¬ p6104) := (Or.elim h66608 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h13772 (fun q0 => (False.elim (u1 q0))) (fun r0 => (False.elim (u3 r0)))))

theorem step74042 (p3794 p3795 p5479 : Prop)
    (h9499 : (¬ p3795) ∨ p5479)
    (h5601 : (¬ p3794) ∨ p3795)
    : p5479 ∨ (¬ p3794) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p5479) := (fun h => hn (Or.inl h));
    let u1 : p3794 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p3795) := (Or.elim h9499 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h5601 (fun q0 => (False.elim (q0 u1))) (fun r0 => (False.elim (u2 r0)))))

theorem step74057 (p2088 p5785 p5786 : Prop)
    (h67267 : (¬ p5786) ∨ (¬ p5785))
    (h11719 : p2088 ∨ p5786)
    : p2088 ∨ (¬ p5785) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2088) := (fun h => hn (Or.inl h));
    let u1 : p5785 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5786) := (Or.elim h67267 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11719 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74059 (p2088 p3857 p5785 p5786 : Prop)
    (h67267 : (¬ p5786) ∨ (¬ p5785))
    (h11713 : p3857 ∨ p5785)
    (h10030 : (¬ p2088) ∨ (¬ p3857))
    : (¬ p2088) ∨ (¬ p5786) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2088 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5786 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5785) := (Or.elim h67267 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3857 := (Or.elim h11713 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10030 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74061 (p2122 p5788 p5789 : Prop)
    (h66504 : (¬ p5789) ∨ (¬ p5788))
    (h11739 : p2122 ∨ p5789)
    : p2122 ∨ (¬ p5788) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2122) := (fun h => hn (Or.inl h));
    let u1 : p5788 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5789) := (Or.elim h66504 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11739 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74063 (p2122 p3822 p5788 p5789 : Prop)
    (h66504 : (¬ p5789) ∨ (¬ p5788))
    (h11732 : p3822 ∨ p5788)
    (h9529 : (¬ p2122) ∨ (¬ p3822))
    : (¬ p2122) ∨ (¬ p5789) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2122 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5789 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5788) := (Or.elim h66504 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3822 := (Or.elim h11732 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9529 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74065 (p2156 p5791 p5792 : Prop)
    (h66505 : (¬ p5792) ∨ (¬ p5791))
    (h11757 : p2156 ∨ p5792)
    : p2156 ∨ (¬ p5791) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2156) := (fun h => hn (Or.inl h));
    let u1 : p5791 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5792) := (Or.elim h66505 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11757 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74067 (p2156 p3646 p5791 p5792 : Prop)
    (h66505 : (¬ p5792) ∨ (¬ p5791))
    (h11750 : p3646 ∨ p5791)
    (h9937 : (¬ p2156) ∨ (¬ p3646))
    : (¬ p2156) ∨ (¬ p5792) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5792 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5791) := (Or.elim h66505 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3646 := (Or.elim h11750 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9937 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74069 (p2166 p5794 p5795 : Prop)
    (h66506 : (¬ p5794) ∨ (¬ p5795))
    (h11774 : p2166 ∨ p5795)
    : p2166 ∨ (¬ p5794) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2166) := (fun h => hn (Or.inl h));
    let u1 : p5794 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5795) := (Or.elim h66506 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11774 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74071 (p2166 p2191 p5794 p5795 : Prop)
    (h66506 : (¬ p5794) ∨ (¬ p5795))
    (h11767 : p2191 ∨ p5794)
    (h9935 : (¬ p2166) ∨ (¬ p2191))
    : (¬ p2166) ∨ (¬ p5795) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5795 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5794) := (Or.elim h66506 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2191 := (Or.elim h11767 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9935 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74073 (p2177 p5797 p5798 : Prop)
    (h66507 : (¬ p5798) ∨ (¬ p5797))
    (h11791 : p2177 ∨ p5798)
    : p2177 ∨ (¬ p5797) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : p5797 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5798) := (Or.elim h66507 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11791 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74075 (p2177 p2299 p5797 p5798 : Prop)
    (h66507 : (¬ p5798) ∨ (¬ p5797))
    (h11784 : p2299 ∨ p5797)
    (h9035 : (¬ p2177) ∨ (¬ p2299))
    : (¬ p2177) ∨ (¬ p5798) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5798 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5797) := (Or.elim h66507 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p2299 := (Or.elim h11784 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9035 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74077 (p2187 p5800 p5801 : Prop)
    (h66508 : (¬ p5801) ∨ (¬ p5800))
    (h11808 : p2187 ∨ p5801)
    : p2187 ∨ (¬ p5800) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2187) := (fun h => hn (Or.inl h));
    let u1 : p5800 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5801) := (Or.elim h66508 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11808 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74079 (p2187 p3989 p5800 p5801 : Prop)
    (h66508 : (¬ p5801) ∨ (¬ p5800))
    (h11801 : p3989 ∨ p5800)
    (h10185 : (¬ p2187) ∨ (¬ p3989))
    : (¬ p2187) ∨ (¬ p5801) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5801 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5800) := (Or.elim h66508 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3989 := (Or.elim h11801 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10185 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74081 (p2192 p5803 p5804 : Prop)
    (h66509 : (¬ p5803) ∨ (¬ p5804))
    (h11825 : p2192 ∨ p5804)
    : p2192 ∨ (¬ p5803) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2192) := (fun h => hn (Or.inl h));
    let u1 : p5803 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5804) := (Or.elim h66509 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11825 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74083 (p2192 p4173 p5803 p5804 : Prop)
    (h66509 : (¬ p5803) ∨ (¬ p5804))
    (h11819 : p4173 ∨ p5803)
    (h9774 : (¬ p2192) ∨ (¬ p4173))
    : (¬ p2192) ∨ (¬ p5804) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2192 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5804 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5803) := (Or.elim h66509 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4173 := (Or.elim h11819 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9774 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74085 (p2210 p5806 p5807 : Prop)
    (h66510 : (¬ p5807) ∨ (¬ p5806))
    (h11841 : p2210 ∨ p5807)
    : p2210 ∨ (¬ p5806) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2210) := (fun h => hn (Or.inl h));
    let u1 : p5806 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5807) := (Or.elim h66510 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11841 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74087 (p2210 p3555 p5806 p5807 : Prop)
    (h66510 : (¬ p5807) ∨ (¬ p5806))
    (h11837 : p3555 ∨ p5806)
    (h9772 : (¬ p2210) ∨ (¬ p3555))
    : (¬ p2210) ∨ (¬ p5807) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2210 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5807 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5806) := (Or.elim h66510 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3555 := (Or.elim h11837 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9772 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74089 (p2220 p5809 p5810 : Prop)
    (h66511 : (¬ p5809) ∨ (¬ p5810))
    (h11862 : p2220 ∨ p5810)
    : p2220 ∨ (¬ p5809) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2220) := (fun h => hn (Or.inl h));
    let u1 : p5809 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5810) := (Or.elim h66511 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11862 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74091 (p2220 p4120 p5809 p5810 : Prop)
    (h66511 : (¬ p5809) ∨ (¬ p5810))
    (h11855 : p4120 ∨ p5809)
    (h9921 : (¬ p2220) ∨ (¬ p4120))
    : (¬ p2220) ∨ (¬ p5810) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2220 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5810 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5809) := (Or.elim h66511 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4120 := (Or.elim h11855 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9921 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74093 (p2230 p5812 p5813 : Prop)
    (h66512 : (¬ p5812) ∨ (¬ p5813))
    (h11879 : p2230 ∨ p5813)
    : p2230 ∨ (¬ p5812) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2230) := (fun h => hn (Or.inl h));
    let u1 : p5812 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5813) := (Or.elim h66512 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11879 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74095 (p2230 p2589 p5812 p5813 : Prop)
    (h66512 : (¬ p5812) ∨ (¬ p5813))
    (h11872 : p2589 ∨ p5812)
    (h9098 : (¬ p2230) ∨ (¬ p2589))
    : (¬ p2230) ∨ (¬ p5813) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2230 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5813 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5812) := (Or.elim h66512 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2589 := (Or.elim h11872 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9098 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74097 (p2264 p5815 p5816 : Prop)
    (h66513 : (¬ p5816) ∨ (¬ p5815))
    (h11896 : p2264 ∨ p5816)
    : p2264 ∨ (¬ p5815) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2264) := (fun h => hn (Or.inl h));
    let u1 : p5815 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5816) := (Or.elim h66513 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11896 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74099 (p2264 p3553 p5815 p5816 : Prop)
    (h66513 : (¬ p5816) ∨ (¬ p5815))
    (h11889 : p3553 ∨ p5815)
    (h10834 : (¬ p2264) ∨ (¬ p3553))
    : (¬ p2264) ∨ (¬ p5816) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2264 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5816 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5815) := (Or.elim h66513 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3553 := (Or.elim h11889 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10834 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74101 (p2274 p5818 p5819 : Prop)
    (h66514 : (¬ p5818) ∨ (¬ p5819))
    (h11913 : p2274 ∨ p5819)
    : p2274 ∨ (¬ p5818) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p5818 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5819) := (Or.elim h66514 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11913 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74103 (p2274 p3097 p5818 p5819 : Prop)
    (h66514 : (¬ p5818) ∨ (¬ p5819))
    (h11906 : p3097 ∨ p5818)
    (h9860 : (¬ p2274) ∨ (¬ p3097))
    : (¬ p2274) ∨ (¬ p5819) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5819 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5818) := (Or.elim h66514 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3097 := (Or.elim h11906 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9860 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74105 (p2284 p5821 p5822 : Prop)
    (h66515 : (¬ p5822) ∨ (¬ p5821))
    (h11930 : p2284 ∨ p5822)
    : p2284 ∨ (¬ p5821) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p5821 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5822) := (Or.elim h66515 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11930 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74107 (p2284 p3952 p5821 p5822 : Prop)
    (h66515 : (¬ p5822) ∨ (¬ p5821))
    (h11923 : p3952 ∨ p5821)
    (h8201 : (¬ p2284) ∨ (¬ p3952))
    : (¬ p2284) ∨ (¬ p5822) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5822 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5821) := (Or.elim h66515 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3952 := (Or.elim h11923 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8201 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74109 (p2295 p5824 p5825 : Prop)
    (h66516 : (¬ p5825) ∨ (¬ p5824))
    (h11948 : p2295 ∨ p5825)
    : p2295 ∨ (¬ p5824) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p5824 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5825) := (Or.elim h66516 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11948 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74111 (p2295 p3568 p5824 p5825 : Prop)
    (h66516 : (¬ p5825) ∨ (¬ p5824))
    (h11941 : p3568 ∨ p5824)
    (h9824 : (¬ p2295) ∨ (¬ p3568))
    : (¬ p2295) ∨ (¬ p5825) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2295 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5825 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5824) := (Or.elim h66516 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3568 := (Or.elim h11941 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9824 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74113 (p2331 p5827 p5828 : Prop)
    (h66517 : (¬ p5827) ∨ (¬ p5828))
    (h11964 : p2331 ∨ p5828)
    : p2331 ∨ (¬ p5827) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2331) := (fun h => hn (Or.inl h));
    let u1 : p5827 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5828) := (Or.elim h66517 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h11964 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74115 (p2331 p2963 p5827 p5828 : Prop)
    (h66517 : (¬ p5827) ∨ (¬ p5828))
    (h11959 : p2963 ∨ p5827)
    (h8311 : (¬ p2331) ∨ (¬ p2963))
    : (¬ p2331) ∨ (¬ p5828) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2331 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5828 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5827) := (Or.elim h66517 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2963 := (Or.elim h11959 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8311 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74117 (p2341 p5830 p5831 : Prop)
    (h66518 : (¬ p5831) ∨ (¬ p5830))
    (h11984 : p2341 ∨ p5831)
    : p2341 ∨ (¬ p5830) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p5830 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5831) := (Or.elim h66518 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11984 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74119 (p2341 p3551 p5830 p5831 : Prop)
    (h66518 : (¬ p5831) ∨ (¬ p5830))
    (h11977 : p3551 ∨ p5830)
    (h9121 : (¬ p2341) ∨ (¬ p3551))
    : (¬ p2341) ∨ (¬ p5831) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5831 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5830) := (Or.elim h66518 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3551 := (Or.elim h11977 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9121 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74121 (p2352 p5833 p5834 : Prop)
    (h66519 : (¬ p5834) ∨ (¬ p5833))
    (h11999 : p2352 ∨ p5834)
    : p2352 ∨ (¬ p5833) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2352) := (fun h => hn (Or.inl h));
    let u1 : p5833 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5834) := (Or.elim h66519 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h11999 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74123 (p2352 p3956 p5833 p5834 : Prop)
    (h66519 : (¬ p5834) ∨ (¬ p5833))
    (h11992 : p3956 ∨ p5833)
    (h9936 : (¬ p2352) ∨ (¬ p3956))
    : (¬ p2352) ∨ (¬ p5834) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5834 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5833) := (Or.elim h66519 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3956 := (Or.elim h11992 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9936 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74125 (p2363 p5836 p5837 : Prop)
    (h66520 : (¬ p5837) ∨ (¬ p5836))
    (h12018 : p2363 ∨ p5837)
    : p2363 ∨ (¬ p5836) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p5836 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5837) := (Or.elim h66520 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12018 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74127 (p2363 p4347 p5836 p5837 : Prop)
    (h66520 : (¬ p5837) ∨ (¬ p5836))
    (h12011 : p4347 ∨ p5836)
    (h9150 : (¬ p2363) ∨ (¬ p4347))
    : (¬ p2363) ∨ (¬ p5837) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2363 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5837 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5836) := (Or.elim h66520 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4347 := (Or.elim h12011 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9150 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74129 (p2373 p5839 p5840 : Prop)
    (h66521 : (¬ p5840) ∨ (¬ p5839))
    (h12037 : p2373 ∨ p5840)
    : p2373 ∨ (¬ p5839) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2373) := (fun h => hn (Or.inl h));
    let u1 : p5839 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5840) := (Or.elim h66521 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12037 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74131 (p2373 p3880 p5839 p5840 : Prop)
    (h66521 : (¬ p5840) ∨ (¬ p5839))
    (h12030 : p3880 ∨ p5839)
    (h10253 : (¬ p2373) ∨ (¬ p3880))
    : (¬ p2373) ∨ (¬ p5840) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2373 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5840 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5839) := (Or.elim h66521 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3880 := (Or.elim h12030 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10253 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74133 (p2383 p5842 p5843 : Prop)
    (h66522 : (¬ p5843) ∨ (¬ p5842))
    (h12053 : p2383 ∨ p5843)
    : p2383 ∨ (¬ p5842) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2383) := (fun h => hn (Or.inl h));
    let u1 : p5842 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5843) := (Or.elim h66522 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12053 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74135 (p2383 p2387 p5842 p5843 : Prop)
    (h66522 : (¬ p5843) ∨ (¬ p5842))
    (h12047 : p2387 ∨ p5842)
    (h9785 : (¬ p2383) ∨ (¬ p2387))
    : (¬ p2383) ∨ (¬ p5843) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5843 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5842) := (Or.elim h66522 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p2387 := (Or.elim h12047 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9785 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74137 (p2396 p5845 p5846 : Prop)
    (h66523 : (¬ p5845) ∨ (¬ p5846))
    (h12072 : p2396 ∨ p5846)
    : p2396 ∨ (¬ p5845) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2396) := (fun h => hn (Or.inl h));
    let u1 : p5845 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5846) := (Or.elim h66523 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12072 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74139 (p2396 p4107 p5845 p5846 : Prop)
    (h66523 : (¬ p5845) ∨ (¬ p5846))
    (h12065 : p4107 ∨ p5845)
    (h8720 : (¬ p2396) ∨ (¬ p4107))
    : (¬ p2396) ∨ (¬ p5846) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5846 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5845) := (Or.elim h66523 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4107 := (Or.elim h12065 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8720 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74141 (p2406 p5848 p5849 : Prop)
    (h66524 : (¬ p5848) ∨ (¬ p5849))
    (h12091 : p2406 ∨ p5849)
    : p2406 ∨ (¬ p5848) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2406) := (fun h => hn (Or.inl h));
    let u1 : p5848 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5849) := (Or.elim h66524 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12091 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74143 (p2406 p3238 p5848 p5849 : Prop)
    (h66524 : (¬ p5848) ∨ (¬ p5849))
    (h12084 : p3238 ∨ p5848)
    (h8977 : (¬ p2406) ∨ (¬ p3238))
    : (¬ p2406) ∨ (¬ p5849) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5849 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5848) := (Or.elim h66524 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3238 := (Or.elim h12084 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8977 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74145 (p2417 p5851 p5852 : Prop)
    (h66525 : (¬ p5851) ∨ (¬ p5852))
    (h12108 : p2417 ∨ p5852)
    : p2417 ∨ (¬ p5851) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p5851 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5852) := (Or.elim h66525 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12108 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74147 (p2417 p4278 p5851 p5852 : Prop)
    (h66525 : (¬ p5851) ∨ (¬ p5852))
    (h12101 : p4278 ∨ p5851)
    (h9835 : (¬ p2417) ∨ (¬ p4278))
    : (¬ p2417) ∨ (¬ p5852) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5852 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5851) := (Or.elim h66525 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4278 := (Or.elim h12101 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9835 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74149 (p2427 p5854 p5855 : Prop)
    (h66526 : (¬ p5854) ∨ (¬ p5855))
    (h12125 : p2427 ∨ p5855)
    : p2427 ∨ (¬ p5854) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2427) := (fun h => hn (Or.inl h));
    let u1 : p5854 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5855) := (Or.elim h66526 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12125 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74151 (p2427 p4235 p5854 p5855 : Prop)
    (h66526 : (¬ p5854) ∨ (¬ p5855))
    (h12118 : p4235 ∨ p5854)
    (h9416 : (¬ p2427) ∨ (¬ p4235))
    : (¬ p2427) ∨ (¬ p5855) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2427 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5855 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5854) := (Or.elim h66526 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4235 := (Or.elim h12118 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9416 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74153 (p2437 p5857 p5858 : Prop)
    (h66527 : (¬ p5858) ∨ (¬ p5857))
    (h12142 : p2437 ∨ p5858)
    : p2437 ∨ (¬ p5857) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : p5857 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5858) := (Or.elim h66527 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12142 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74155 (p2437 p3742 p5857 p5858 : Prop)
    (h66527 : (¬ p5858) ∨ (¬ p5857))
    (h12135 : p3742 ∨ p5857)
    (h9612 : (¬ p2437) ∨ (¬ p3742))
    : (¬ p2437) ∨ (¬ p5858) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2437 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5858 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5857) := (Or.elim h66527 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3742 := (Or.elim h12135 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9612 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74157 (p2449 p5860 p5861 : Prop)
    (h66528 : (¬ p5860) ∨ (¬ p5861))
    (h12159 : p2449 ∨ p5861)
    : p2449 ∨ (¬ p5860) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p5860 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5861) := (Or.elim h66528 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12159 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74159 (p2449 p3947 p5860 p5861 : Prop)
    (h66528 : (¬ p5860) ∨ (¬ p5861))
    (h12152 : p3947 ∨ p5860)
    (h10864 : (¬ p2449) ∨ (¬ p3947))
    : (¬ p2449) ∨ (¬ p5861) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5861 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5860) := (Or.elim h66528 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3947 := (Or.elim h12152 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10864 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74161 (p2459 p5863 p5864 : Prop)
    (h66529 : (¬ p5863) ∨ (¬ p5864))
    (h12176 : p2459 ∨ p5864)
    : p2459 ∨ (¬ p5863) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : p5863 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5864) := (Or.elim h66529 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12176 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74163 (p2459 p4348 p5863 p5864 : Prop)
    (h66529 : (¬ p5863) ∨ (¬ p5864))
    (h12169 : p4348 ∨ p5863)
    (h9286 : (¬ p2459) ∨ (¬ p4348))
    : (¬ p2459) ∨ (¬ p5864) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2459 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5864 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5863) := (Or.elim h66529 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4348 := (Or.elim h12169 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9286 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74165 (p2528 p5869 p5870 : Prop)
    (h66531 : (¬ p5869) ∨ (¬ p5870))
    (h12213 : p2528 ∨ p5870)
    : p2528 ∨ (¬ p5869) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p5869 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5870) := (Or.elim h66531 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12213 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74167 (p2528 p2534 p5869 p5870 : Prop)
    (h66531 : (¬ p5869) ∨ (¬ p5870))
    (h12206 : p2534 ∨ p5869)
    (h8701 : (¬ p2528) ∨ (¬ p2534))
    : (¬ p2528) ∨ (¬ p5870) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5870 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5869) := (Or.elim h66531 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2534 := (Or.elim h12206 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8701 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74169 (p2440 p2542 p5872 p5873 : Prop)
    (h66532 : (¬ p5873) ∨ (¬ p5872))
    (h12230 : p2542 ∨ p5873)
    (h9451 : (¬ p2440) ∨ (¬ p2542))
    : (¬ p2440) ∨ (¬ p5872) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2440 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5872 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5873) := (Or.elim h66532 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p2542 := (Or.elim h12230 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9451 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74171 (p2440 p5872 p5873 : Prop)
    (h66532 : (¬ p5873) ∨ (¬ p5872))
    (h12223 : p2440 ∨ p5872)
    : p2440 ∨ (¬ p5873) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p5873 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5872) := (Or.elim h66532 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12223 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74173 (p2553 p5875 p5876 : Prop)
    (h66533 : (¬ p5876) ∨ (¬ p5875))
    (h12248 : p2553 ∨ p5876)
    : p2553 ∨ (¬ p5875) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p5875 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5876) := (Or.elim h66533 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12248 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74175 (p2553 p2588 p5875 p5876 : Prop)
    (h66533 : (¬ p5876) ∨ (¬ p5875))
    (h12241 : p2588 ∨ p5875)
    (h9753 : (¬ p2553) ∨ (¬ p2588))
    : (¬ p2553) ∨ (¬ p5876) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5876 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5875) := (Or.elim h66533 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p2588 := (Or.elim h12241 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9753 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74177 (p2563 p5878 p5879 : Prop)
    (h66534 : (¬ p5878) ∨ (¬ p5879))
    (h12265 : p2563 ∨ p5879)
    : p2563 ∨ (¬ p5878) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2563) := (fun h => hn (Or.inl h));
    let u1 : p5878 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5879) := (Or.elim h66534 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12265 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74179 (p2563 p4110 p5878 p5879 : Prop)
    (h66534 : (¬ p5878) ∨ (¬ p5879))
    (h12258 : p4110 ∨ p5878)
    (h9440 : (¬ p2563) ∨ (¬ p4110))
    : (¬ p2563) ∨ (¬ p5879) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2563 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5879 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5878) := (Or.elim h66534 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4110 := (Or.elim h12258 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9440 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74181 (p2598 p5881 p5882 : Prop)
    (h66535 : (¬ p5882) ∨ (¬ p5881))
    (h12280 : p2598 ∨ p5882)
    : p2598 ∨ (¬ p5881) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2598) := (fun h => hn (Or.inl h));
    let u1 : p5881 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5882) := (Or.elim h66535 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12280 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74183 (p2598 p3055 p5881 p5882 : Prop)
    (h66535 : (¬ p5882) ∨ (¬ p5881))
    (h12276 : p3055 ∨ p5881)
    (h9095 : (¬ p2598) ∨ (¬ p3055))
    : (¬ p2598) ∨ (¬ p5882) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2598 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5882 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5881) := (Or.elim h66535 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3055 := (Or.elim h12276 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9095 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74185 (p2608 p5884 p5885 : Prop)
    (h66536 : (¬ p5884) ∨ (¬ p5885))
    (h12300 : p2608 ∨ p5885)
    : p2608 ∨ (¬ p5884) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2608) := (fun h => hn (Or.inl h));
    let u1 : p5884 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5885) := (Or.elim h66536 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12300 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74187 (p2608 p3954 p5884 p5885 : Prop)
    (h66536 : (¬ p5884) ∨ (¬ p5885))
    (h12292 : p3954 ∨ p5884)
    (h9054 : (¬ p2608) ∨ (¬ p3954))
    : (¬ p2608) ∨ (¬ p5885) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2608 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5885 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5884) := (Or.elim h66536 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3954 := (Or.elim h12292 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9054 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74189 (p2619 p5887 p5888 : Prop)
    (h66537 : (¬ p5887) ∨ (¬ p5888))
    (h12316 : p2619 ∨ p5888)
    : p2619 ∨ (¬ p5887) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2619) := (fun h => hn (Or.inl h));
    let u1 : p5887 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5888) := (Or.elim h66537 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12316 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74191 (p2619 p3694 p5887 p5888 : Prop)
    (h66537 : (¬ p5887) ∨ (¬ p5888))
    (h12309 : p3694 ∨ p5887)
    (h9933 : (¬ p2619) ∨ (¬ p3694))
    : (¬ p2619) ∨ (¬ p5888) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2619 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5888 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5887) := (Or.elim h66537 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3694 := (Or.elim h12309 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9933 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74193 (p2630 p5890 p5891 : Prop)
    (h66538 : (¬ p5891) ∨ (¬ p5890))
    (h12333 : p2630 ∨ p5891)
    : p2630 ∨ (¬ p5890) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2630) := (fun h => hn (Or.inl h));
    let u1 : p5890 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5891) := (Or.elim h66538 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12333 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74195 (p2630 p2810 p5890 p5891 : Prop)
    (h66538 : (¬ p5891) ∨ (¬ p5890))
    (h12326 : p2810 ∨ p5890)
    (h9606 : (¬ p2630) ∨ (¬ p2810))
    : (¬ p2630) ∨ (¬ p5891) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2630 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5891 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5890) := (Or.elim h66538 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p2810 := (Or.elim h12326 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9606 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74197 (p2641 p5893 p5894 : Prop)
    (h66539 : (¬ p5894) ∨ (¬ p5893))
    (h12349 : p2641 ∨ p5894)
    : p2641 ∨ (¬ p5893) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2641) := (fun h => hn (Or.inl h));
    let u1 : p5893 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5894) := (Or.elim h66539 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12349 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74199 (p2641 p4154 p5893 p5894 : Prop)
    (h66539 : (¬ p5894) ∨ (¬ p5893))
    (h12347 : p4154 ∨ p5893)
    (h10070 : (¬ p2641) ∨ (¬ p4154))
    : (¬ p2641) ∨ (¬ p5894) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5894 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5893) := (Or.elim h66539 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4154 := (Or.elim h12347 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10070 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74201 (p2668 p5896 p5897 : Prop)
    (h66540 : (¬ p5897) ∨ (¬ p5896))
    (h12368 : p2668 ∨ p5897)
    : p2668 ∨ (¬ p5896) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2668) := (fun h => hn (Or.inl h));
    let u1 : p5896 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5897) := (Or.elim h66540 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12368 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74203 (p2668 p3324 p5896 p5897 : Prop)
    (h66540 : (¬ p5897) ∨ (¬ p5896))
    (h12361 : p3324 ∨ p5896)
    (h9896 : (¬ p2668) ∨ (¬ p3324))
    : (¬ p2668) ∨ (¬ p5897) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2668 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5897 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5896) := (Or.elim h66540 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3324 := (Or.elim h12361 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9896 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74205 (p2685 p5899 p5900 : Prop)
    (h66541 : (¬ p5899) ∨ (¬ p5900))
    (h12385 : p2685 ∨ p5900)
    : p2685 ∨ (¬ p5899) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2685) := (fun h => hn (Or.inl h));
    let u1 : p5899 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5900) := (Or.elim h66541 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12385 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74207 (p2685 p3572 p5899 p5900 : Prop)
    (h66541 : (¬ p5899) ∨ (¬ p5900))
    (h12378 : p3572 ∨ p5899)
    (h11420 : (¬ p2685) ∨ (¬ p3572))
    : (¬ p2685) ∨ (¬ p5900) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2685 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5900 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5899) := (Or.elim h66541 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3572 := (Or.elim h12378 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11420 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74209 (p2696 p5902 p5903 : Prop)
    (h66542 : (¬ p5902) ∨ (¬ p5903))
    (h12403 : p2696 ∨ p5903)
    : p2696 ∨ (¬ p5902) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2696) := (fun h => hn (Or.inl h));
    let u1 : p5902 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5903) := (Or.elim h66542 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12403 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74211 (p2696 p3365 p5902 p5903 : Prop)
    (h66542 : (¬ p5902) ∨ (¬ p5903))
    (h12395 : p3365 ∨ p5902)
    (h9080 : (¬ p2696) ∨ (¬ p3365))
    : (¬ p2696) ∨ (¬ p5903) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2696 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5903 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5902) := (Or.elim h66542 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3365 := (Or.elim h12395 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9080 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74213 (p2707 p5905 p5906 : Prop)
    (h66543 : (¬ p5905) ∨ (¬ p5906))
    (h12421 : p2707 ∨ p5906)
    : p2707 ∨ (¬ p5905) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2707) := (fun h => hn (Or.inl h));
    let u1 : p5905 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5906) := (Or.elim h66543 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12421 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74215 (p2707 p3588 p5905 p5906 : Prop)
    (h66543 : (¬ p5905) ∨ (¬ p5906))
    (h12415 : p3588 ∨ p5905)
    (h9154 : (¬ p2707) ∨ (¬ p3588))
    : (¬ p2707) ∨ (¬ p5906) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5906 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5905) := (Or.elim h66543 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3588 := (Or.elim h12415 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9154 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74217 (p2717 p5908 p5909 : Prop)
    (h66544 : (¬ p5909) ∨ (¬ p5908))
    (h12438 : p2717 ∨ p5909)
    : p2717 ∨ (¬ p5908) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2717) := (fun h => hn (Or.inl h));
    let u1 : p5908 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5909) := (Or.elim h66544 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12438 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74219 (p2717 p3659 p5908 p5909 : Prop)
    (h66544 : (¬ p5909) ∨ (¬ p5908))
    (h12431 : p3659 ∨ p5908)
    (h10204 : (¬ p2717) ∨ (¬ p3659))
    : (¬ p2717) ∨ (¬ p5909) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5909 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5908) := (Or.elim h66544 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3659 := (Or.elim h12431 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10204 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74221 (p2727 p5911 p5912 : Prop)
    (h66545 : (¬ p5911) ∨ (¬ p5912))
    (h12456 : p2727 ∨ p5912)
    : p2727 ∨ (¬ p5911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2727) := (fun h => hn (Or.inl h));
    let u1 : p5911 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5912) := (Or.elim h66545 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12456 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74223 (p2727 p4111 p5911 p5912 : Prop)
    (h66545 : (¬ p5911) ∨ (¬ p5912))
    (h12449 : p4111 ∨ p5911)
    (h7872 : (¬ p2727) ∨ (¬ p4111))
    : (¬ p2727) ∨ (¬ p5912) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5912 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5911) := (Or.elim h66545 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4111 := (Or.elim h12449 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h7872 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74225 (p2761 p5914 p5915 : Prop)
    (h66546 : (¬ p5915) ∨ (¬ p5914))
    (h12473 : p2761 ∨ p5915)
    : p2761 ∨ (¬ p5914) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2761) := (fun h => hn (Or.inl h));
    let u1 : p5914 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5915) := (Or.elim h66546 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12473 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74227 (p2761 p4381 p5914 p5915 : Prop)
    (h66546 : (¬ p5915) ∨ (¬ p5914))
    (h12466 : p4381 ∨ p5914)
    (h10478 : (¬ p2761) ∨ (¬ p4381))
    : (¬ p2761) ∨ (¬ p5915) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2761 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5915 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5914) := (Or.elim h66546 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4381 := (Or.elim h12466 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10478 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74229 (p2797 p5917 p5918 : Prop)
    (h66547 : (¬ p5918) ∨ (¬ p5917))
    (h12493 : p2797 ∨ p5918)
    : p2797 ∨ (¬ p5917) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2797) := (fun h => hn (Or.inl h));
    let u1 : p5917 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5918) := (Or.elim h66547 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12493 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74231 (p2797 p4195 p5917 p5918 : Prop)
    (h66547 : (¬ p5918) ∨ (¬ p5917))
    (h12486 : p4195 ∨ p5917)
    (h10905 : (¬ p2797) ∨ (¬ p4195))
    : (¬ p2797) ∨ (¬ p5918) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2797 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5918 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5917) := (Or.elim h66547 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4195 := (Or.elim h12486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10905 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74233 (p2807 p5920 p5921 : Prop)
    (h67268 : (¬ p5920) ∨ (¬ p5921))
    (h12512 : p2807 ∨ p5921)
    : p2807 ∨ (¬ p5920) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2807) := (fun h => hn (Or.inl h));
    let u1 : p5920 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5921) := (Or.elim h67268 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12512 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74235 (p2807 p3414 p5920 p5921 : Prop)
    (h67268 : (¬ p5920) ∨ (¬ p5921))
    (h12503 : p3414 ∨ p5920)
    (h9096 : (¬ p2807) ∨ (¬ p3414))
    : (¬ p2807) ∨ (¬ p5921) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2807 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5921 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5920) := (Or.elim h67268 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3414 := (Or.elim h12503 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9096 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74237 (p2819 p5923 p5924 : Prop)
    (h66548 : (¬ p5923) ∨ (¬ p5924))
    (h12532 : p2819 ∨ p5924)
    : p2819 ∨ (¬ p5923) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2819) := (fun h => hn (Or.inl h));
    let u1 : p5923 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5924) := (Or.elim h66548 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12532 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74239 (p2819 p4358 p5923 p5924 : Prop)
    (h66548 : (¬ p5923) ∨ (¬ p5924))
    (h12525 : p4358 ∨ p5923)
    (h10948 : (¬ p2819) ∨ (¬ p4358))
    : (¬ p2819) ∨ (¬ p5924) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2819 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5924 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5923) := (Or.elim h66548 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4358 := (Or.elim h12525 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10948 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74241 (p2829 p5926 p5927 : Prop)
    (h66549 : (¬ p5926) ∨ (¬ p5927))
    (h12552 : p2829 ∨ p5927)
    : p2829 ∨ (¬ p5926) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2829) := (fun h => hn (Or.inl h));
    let u1 : p5926 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5927) := (Or.elim h66549 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12552 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74243 (p2829 p3688 p5926 p5927 : Prop)
    (h66549 : (¬ p5926) ∨ (¬ p5927))
    (h12542 : p3688 ∨ p5926)
    (h10789 : (¬ p2829) ∨ (¬ p3688))
    : (¬ p2829) ∨ (¬ p5927) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2829 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5927 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5926) := (Or.elim h66549 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3688 := (Or.elim h12542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10789 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74245 (p2839 p5929 p5930 : Prop)
    (h66550 : (¬ p5929) ∨ (¬ p5930))
    (h12568 : p2839 ∨ p5930)
    : p2839 ∨ (¬ p5929) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2839) := (fun h => hn (Or.inl h));
    let u1 : p5929 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5930) := (Or.elim h66550 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12568 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74247 (p2839 p3583 p5929 p5930 : Prop)
    (h66550 : (¬ p5929) ∨ (¬ p5930))
    (h12559 : p3583 ∨ p5929)
    (h9144 : (¬ p2839) ∨ (¬ p3583))
    : (¬ p2839) ∨ (¬ p5930) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2839 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5930 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5929) := (Or.elim h66550 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3583 := (Or.elim h12559 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9144 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74249 (p2850 p5932 p5933 : Prop)
    (h66551 : (¬ p5932) ∨ (¬ p5933))
    (h12584 : p2850 ∨ p5933)
    : p2850 ∨ (¬ p5932) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2850) := (fun h => hn (Or.inl h));
    let u1 : p5932 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5933) := (Or.elim h66551 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12584 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74251 (p2850 p3684 p5932 p5933 : Prop)
    (h66551 : (¬ p5932) ∨ (¬ p5933))
    (h12577 : p3684 ∨ p5932)
    (h9415 : (¬ p2850) ∨ (¬ p3684))
    : (¬ p2850) ∨ (¬ p5933) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2850 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5933 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5932) := (Or.elim h66551 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3684 := (Or.elim h12577 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9415 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74253 (p2860 p5935 p5936 : Prop)
    (h66552 : (¬ p5935) ∨ (¬ p5936))
    (h12601 : p2860 ∨ p5936)
    : p2860 ∨ (¬ p5935) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2860) := (fun h => hn (Or.inl h));
    let u1 : p5935 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5936) := (Or.elim h66552 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12601 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74255 (p2860 p3758 p5935 p5936 : Prop)
    (h66552 : (¬ p5935) ∨ (¬ p5936))
    (h12594 : p3758 ∨ p5935)
    (h10610 : (¬ p2860) ∨ (¬ p3758))
    : (¬ p2860) ∨ (¬ p5936) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2860 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5936 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5935) := (Or.elim h66552 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3758 := (Or.elim h12594 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10610 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74257 (p2870 p5938 p5939 : Prop)
    (h66553 : (¬ p5939) ∨ (¬ p5938))
    (h12619 : p2870 ∨ p5939)
    : p2870 ∨ (¬ p5938) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2870) := (fun h => hn (Or.inl h));
    let u1 : p5938 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5939) := (Or.elim h66553 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12619 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74259 (p2870 p4244 p5938 p5939 : Prop)
    (h66553 : (¬ p5939) ∨ (¬ p5938))
    (h12612 : p4244 ∨ p5938)
    (h9153 : (¬ p2870) ∨ (¬ p4244))
    : (¬ p2870) ∨ (¬ p5939) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2870 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5939 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5938) := (Or.elim h66553 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4244 := (Or.elim h12612 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9153 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74261 (p2881 p5941 p5942 : Prop)
    (h66554 : (¬ p5942) ∨ (¬ p5941))
    (h12638 : p2881 ∨ p5942)
    : p2881 ∨ (¬ p5941) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p5941 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5942) := (Or.elim h66554 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12638 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74263 (p2881 p3570 p5941 p5942 : Prop)
    (h66554 : (¬ p5942) ∨ (¬ p5941))
    (h12631 : p3570 ∨ p5941)
    (h9899 : (¬ p2881) ∨ (¬ p3570))
    : (¬ p2881) ∨ (¬ p5942) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5942 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5941) := (Or.elim h66554 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3570 := (Or.elim h12631 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9899 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74265 (p2891 p5944 p5945 : Prop)
    (h66555 : (¬ p5945) ∨ (¬ p5944))
    (h12655 : p2891 ∨ p5945)
    : p2891 ∨ (¬ p5944) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2891) := (fun h => hn (Or.inl h));
    let u1 : p5944 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5945) := (Or.elim h66555 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12655 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74267 (p2891 p3486 p5944 p5945 : Prop)
    (h66555 : (¬ p5945) ∨ (¬ p5944))
    (h12648 : p3486 ∨ p5944)
    (h10093 : (¬ p2891) ∨ (¬ p3486))
    : (¬ p2891) ∨ (¬ p5945) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2891 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5945 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5944) := (Or.elim h66555 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3486 := (Or.elim h12648 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10093 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74269 (p2901 p5947 p5948 : Prop)
    (h66556 : (¬ p5947) ∨ (¬ p5948))
    (h12672 : p2901 ∨ p5948)
    : p2901 ∨ (¬ p5947) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p5947 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5948) := (Or.elim h66556 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12672 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74271 (p2901 p4320 p5947 p5948 : Prop)
    (h66556 : (¬ p5947) ∨ (¬ p5948))
    (h12665 : p4320 ∨ p5947)
    (h9331 : (¬ p2901) ∨ (¬ p4320))
    : (¬ p2901) ∨ (¬ p5948) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2901 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5948 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5947) := (Or.elim h66556 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4320 := (Or.elim h12665 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9331 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74273 (p2911 p5950 p5951 : Prop)
    (h66557 : (¬ p5951) ∨ (¬ p5950))
    (h12689 : p2911 ∨ p5951)
    : p2911 ∨ (¬ p5950) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : p5950 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5951) := (Or.elim h66557 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12689 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74275 (p2911 p3644 p5950 p5951 : Prop)
    (h66557 : (¬ p5951) ∨ (¬ p5950))
    (h12682 : p3644 ∨ p5950)
    (h9125 : (¬ p2911) ∨ (¬ p3644))
    : (¬ p2911) ∨ (¬ p5951) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5951 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5950) := (Or.elim h66557 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3644 := (Or.elim h12682 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9125 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74277 (p2972 p5953 p5954 : Prop)
    (h66558 : (¬ p5953) ∨ (¬ p5954))
    (h12709 : p2972 ∨ p5954)
    : p2972 ∨ (¬ p5953) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2972) := (fun h => hn (Or.inl h));
    let u1 : p5953 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5954) := (Or.elim h66558 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12709 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74279 (p2972 p4363 p5953 p5954 : Prop)
    (h66558 : (¬ p5953) ∨ (¬ p5954))
    (h12702 : p4363 ∨ p5953)
    (h11583 : (¬ p2972) ∨ (¬ p4363))
    : (¬ p2972) ∨ (¬ p5954) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2972 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5954 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5953) := (Or.elim h66558 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4363 := (Or.elim h12702 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11583 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74281 (p2982 p5956 p5957 : Prop)
    (h66559 : (¬ p5956) ∨ (¬ p5957))
    (h12727 : p2982 ∨ p5957)
    : p2982 ∨ (¬ p5956) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2982) := (fun h => hn (Or.inl h));
    let u1 : p5956 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5957) := (Or.elim h66559 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12727 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74283 (p2982 p4948 p5956 p5957 : Prop)
    (h66559 : (¬ p5956) ∨ (¬ p5957))
    (h12720 : p4948 ∨ p5956)
    (h11585 : (¬ p2982) ∨ (¬ p4948))
    : (¬ p2982) ∨ (¬ p5957) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2982 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5957 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5956) := (Or.elim h66559 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4948 := (Or.elim h12720 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11585 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74285 (p2992 p5959 p5960 : Prop)
    (h66560 : (¬ p5959) ∨ (¬ p5960))
    (h12743 : p2992 ∨ p5960)
    : p2992 ∨ (¬ p5959) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2992) := (fun h => hn (Or.inl h));
    let u1 : p5959 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5960) := (Or.elim h66560 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12743 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74287 (p2992 p3662 p5959 p5960 : Prop)
    (h66560 : (¬ p5959) ∨ (¬ p5960))
    (h12740 : p3662 ∨ p5959)
    (h8869 : (¬ p2992) ∨ (¬ p3662))
    : (¬ p2992) ∨ (¬ p5960) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2992 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5960 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5959) := (Or.elim h66560 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3662 := (Or.elim h12740 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8869 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74289 (p3005 p5962 p5963 : Prop)
    (h66561 : (¬ p5963) ∨ (¬ p5962))
    (h12767 : p3005 ∨ p5963)
    : p3005 ∨ (¬ p5962) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3005) := (fun h => hn (Or.inl h));
    let u1 : p5962 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5963) := (Or.elim h66561 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12767 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74291 (p3005 p3877 p5962 p5963 : Prop)
    (h66561 : (¬ p5963) ∨ (¬ p5962))
    (h12760 : p3877 ∨ p5962)
    (h10321 : (¬ p3005) ∨ (¬ p3877))
    : (¬ p3005) ∨ (¬ p5963) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3005 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5963 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5962) := (Or.elim h66561 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3877 := (Or.elim h12760 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10321 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74293 (p3016 p5965 p5966 : Prop)
    (h66562 : (¬ p5966) ∨ (¬ p5965))
    (h12787 : p3016 ∨ p5966)
    : p3016 ∨ (¬ p5965) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3016) := (fun h => hn (Or.inl h));
    let u1 : p5965 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5966) := (Or.elim h66562 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12787 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74295 (p3016 p3574 p5965 p5966 : Prop)
    (h66562 : (¬ p5966) ∨ (¬ p5965))
    (h12780 : p3574 ∨ p5965)
    (h10212 : (¬ p3016) ∨ (¬ p3574))
    : (¬ p3016) ∨ (¬ p5966) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5966 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5965) := (Or.elim h66562 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3574 := (Or.elim h12780 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10212 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74297 (p3051 p5968 p5969 : Prop)
    (h66563 : (¬ p5968) ∨ (¬ p5969))
    (h12809 : p3051 ∨ p5969)
    : p3051 ∨ (¬ p5968) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3051) := (fun h => hn (Or.inl h));
    let u1 : p5968 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5969) := (Or.elim h66563 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12809 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74299 (p3051 p3556 p5968 p5969 : Prop)
    (h66563 : (¬ p5968) ∨ (¬ p5969))
    (h12803 : p3556 ∨ p5968)
    (h9152 : (¬ p3051) ∨ (¬ p3556))
    : (¬ p3051) ∨ (¬ p5969) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3051 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5969 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5968) := (Or.elim h66563 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3556 := (Or.elim h12803 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9152 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74301 (p3073 p5974 p5975 : Prop)
    (h66565 : (¬ p5975) ∨ (¬ p5974))
    (h12842 : p3073 ∨ p5975)
    : p3073 ∨ (¬ p5974) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3073) := (fun h => hn (Or.inl h));
    let u1 : p5974 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5975) := (Or.elim h66565 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12842 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74303 (p3073 p4261 p5974 p5975 : Prop)
    (h66565 : (¬ p5975) ∨ (¬ p5974))
    (h12835 : p4261 ∨ p5974)
    (h10239 : (¬ p3073) ∨ (¬ p4261))
    : (¬ p3073) ∨ (¬ p5975) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3073 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5975 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5974) := (Or.elim h66565 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p4261 := (Or.elim h12835 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10239 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74305 (p3083 p5977 p5978 : Prop)
    (h66566 : (¬ p5977) ∨ (¬ p5978))
    (h12860 : p3083 ∨ p5978)
    : p3083 ∨ (¬ p5977) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p5977 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5978) := (Or.elim h66566 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12860 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74307 (p3083 p4256 p5977 p5978 : Prop)
    (h66566 : (¬ p5977) ∨ (¬ p5978))
    (h12853 : p4256 ∨ p5977)
    (h10987 : (¬ p3083) ∨ (¬ p4256))
    : (¬ p3083) ∨ (¬ p5978) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3083 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5978 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5977) := (Or.elim h66566 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4256 := (Or.elim h12853 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10987 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74309 (p3093 p5980 p5981 : Prop)
    (h66567 : (¬ p5981) ∨ (¬ p5980))
    (h12876 : p3093 ∨ p5981)
    : p3093 ∨ (¬ p5980) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : p5980 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5981) := (Or.elim h66567 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h12876 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74311 (p3093 p3591 p5980 p5981 : Prop)
    (h66567 : (¬ p5981) ∨ (¬ p5980))
    (h12870 : p3591 ∨ p5980)
    (h8401 : (¬ p3093) ∨ (¬ p3591))
    : (¬ p3093) ∨ (¬ p5981) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3093 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5981 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5980) := (Or.elim h66567 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3591 := (Or.elim h12870 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8401 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74313 (p3105 p5983 p5984 : Prop)
    (h66568 : (¬ p5983) ∨ (¬ p5984))
    (h12895 : p3105 ∨ p5984)
    : p3105 ∨ (¬ p5983) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3105) := (fun h => hn (Or.inl h));
    let u1 : p5983 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5984) := (Or.elim h66568 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12895 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74315 (p3105 p4385 p5983 p5984 : Prop)
    (h66568 : (¬ p5983) ∨ (¬ p5984))
    (h12888 : p4385 ∨ p5983)
    (h10786 : (¬ p3105) ∨ (¬ p4385))
    : (¬ p3105) ∨ (¬ p5984) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3105 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5984 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5983) := (Or.elim h66568 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4385 := (Or.elim h12888 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10786 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74317 (p3115 p5986 p5987 : Prop)
    (h66569 : (¬ p5986) ∨ (¬ p5987))
    (h12913 : p3115 ∨ p5987)
    : p3115 ∨ (¬ p5986) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3115) := (fun h => hn (Or.inl h));
    let u1 : p5986 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5987) := (Or.elim h66569 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12913 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74319 (p3115 p4208 p5986 p5987 : Prop)
    (h66569 : (¬ p5986) ∨ (¬ p5987))
    (h12906 : p4208 ∨ p5986)
    (h11641 : (¬ p3115) ∨ (¬ p4208))
    : (¬ p3115) ∨ (¬ p5987) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3115 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5987 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5986) := (Or.elim h66569 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4208 := (Or.elim h12906 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11641 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74321 (p3125 p5989 p5990 : Prop)
    (h66570 : (¬ p5989) ∨ (¬ p5990))
    (h12930 : p3125 ∨ p5990)
    : p3125 ∨ (¬ p5989) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3125) := (fun h => hn (Or.inl h));
    let u1 : p5989 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5990) := (Or.elim h66570 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12930 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74323 (p3125 p3744 p5989 p5990 : Prop)
    (h66570 : (¬ p5989) ∨ (¬ p5990))
    (h12923 : p3744 ∨ p5989)
    (h9853 : (¬ p3125) ∨ (¬ p3744))
    : (¬ p3125) ∨ (¬ p5990) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3125 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5990 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5989) := (Or.elim h66570 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3744 := (Or.elim h12923 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9853 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74325 (p3136 p5992 p5993 : Prop)
    (h66571 : (¬ p5992) ∨ (¬ p5993))
    (h12948 : p3136 ∨ p5993)
    : p3136 ∨ (¬ p5992) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3136) := (fun h => hn (Or.inl h));
    let u1 : p5992 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5993) := (Or.elim h66571 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12948 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74327 (p3136 p4315 p5992 p5993 : Prop)
    (h66571 : (¬ p5992) ∨ (¬ p5993))
    (h12941 : p4315 ∨ p5992)
    (h10894 : (¬ p3136) ∨ (¬ p4315))
    : (¬ p3136) ∨ (¬ p5993) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3136 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5993 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5992) := (Or.elim h66571 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4315 := (Or.elim h12941 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10894 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74329 (p3146 p5995 p5996 : Prop)
    (h66572 : (¬ p5995) ∨ (¬ p5996))
    (h12965 : p3146 ∨ p5996)
    : p3146 ∨ (¬ p5995) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3146) := (fun h => hn (Or.inl h));
    let u1 : p5995 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5996) := (Or.elim h66572 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12965 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74331 (p3146 p3692 p5995 p5996 : Prop)
    (h66572 : (¬ p5995) ∨ (¬ p5996))
    (h12958 : p3692 ∨ p5995)
    (h9906 : (¬ p3146) ∨ (¬ p3692))
    : (¬ p3146) ∨ (¬ p5996) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3146 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5996 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5995) := (Or.elim h66572 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3692 := (Or.elim h12958 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9906 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74333 (p3156 p5998 p5999 : Prop)
    (h66573 : (¬ p5998) ∨ (¬ p5999))
    (h12982 : p3156 ∨ p5999)
    : p3156 ∨ (¬ p5998) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3156) := (fun h => hn (Or.inl h));
    let u1 : p5998 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5999) := (Or.elim h66573 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h12982 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74335 (p3156 p3497 p5998 p5999 : Prop)
    (h66573 : (¬ p5998) ∨ (¬ p5999))
    (h12975 : p3497 ∨ p5998)
    (h9439 : (¬ p3156) ∨ (¬ p3497))
    : (¬ p3156) ∨ (¬ p5999) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3156 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p5999 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p5998) := (Or.elim h66573 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3497 := (Or.elim h12975 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9439 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74337 (p3189 p6001 p6002 : Prop)
    (h66574 : (¬ p6001) ∨ (¬ p6002))
    (h13002 : p3189 ∨ p6002)
    : p3189 ∨ (¬ p6001) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3189) := (fun h => hn (Or.inl h));
    let u1 : p6001 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6002) := (Or.elim h66574 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13002 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74339 (p3189 p4360 p6001 p6002 : Prop)
    (h66574 : (¬ p6001) ∨ (¬ p6002))
    (h12994 : p4360 ∨ p6001)
    (h10114 : (¬ p3189) ∨ (¬ p4360))
    : (¬ p3189) ∨ (¬ p6002) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3189 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6002 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6001) := (Or.elim h66574 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4360 := (Or.elim h12994 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10114 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74341 (p3201 p6004 p6005 : Prop)
    (h66575 : (¬ p6004) ∨ (¬ p6005))
    (h13022 : p3201 ∨ p6005)
    : p3201 ∨ (¬ p6004) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p6004 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6005) := (Or.elim h66575 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13022 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74343 (p3201 p3876 p6004 p6005 : Prop)
    (h66575 : (¬ p6004) ∨ (¬ p6005))
    (h13015 : p3876 ∨ p6004)
    (h11128 : (¬ p3201) ∨ (¬ p3876))
    : (¬ p3201) ∨ (¬ p6005) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3201 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6005 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6004) := (Or.elim h66575 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3876 := (Or.elim h13015 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11128 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74345 (p3246 p6010 p6011 : Prop)
    (h66577 : (¬ p6010) ∨ (¬ p6011))
    (h13061 : p3246 ∨ p6011)
    : p3246 ∨ (¬ p6010) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p6010 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6011) := (Or.elim h66577 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13061 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74347 (p3246 p3690 p6010 p6011 : Prop)
    (h66577 : (¬ p6010) ∨ (¬ p6011))
    (h13054 : p3690 ∨ p6010)
    (h10589 : (¬ p3246) ∨ (¬ p3690))
    : (¬ p3246) ∨ (¬ p6011) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6011 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6010) := (Or.elim h66577 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3690 := (Or.elim h13054 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10589 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74349 (p3256 p6013 p6014 : Prop)
    (h66578 : (¬ p6013) ∨ (¬ p6014))
    (h13081 : p3256 ∨ p6014)
    : p3256 ∨ (¬ p6013) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p6013 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6014) := (Or.elim h66578 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13081 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74351 (p3256 p4118 p6013 p6014 : Prop)
    (h66578 : (¬ p6013) ∨ (¬ p6014))
    (h13074 : p4118 ∨ p6013)
    (h10930 : (¬ p3256) ∨ (¬ p4118))
    : (¬ p3256) ∨ (¬ p6014) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3256 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6014 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6013) := (Or.elim h66578 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4118 := (Or.elim h13074 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10930 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74353 (p3266 p6016 p6017 : Prop)
    (h66579 : (¬ p6016) ∨ (¬ p6017))
    (h13099 : p3266 ∨ p6017)
    : p3266 ∨ (¬ p6016) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3266) := (fun h => hn (Or.inl h));
    let u1 : p6016 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6017) := (Or.elim h66579 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13099 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74355 (p3266 p4444 p6016 p6017 : Prop)
    (h66579 : (¬ p6016) ∨ (¬ p6017))
    (h13092 : p4444 ∨ p6016)
    (h11336 : (¬ p3266) ∨ (¬ p4444))
    : (¬ p3266) ∨ (¬ p6017) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3266 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6017 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6016) := (Or.elim h66579 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4444 := (Or.elim h13092 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11336 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74357 (p3276 p6019 p6020 : Prop)
    (h66580 : (¬ p6019) ∨ (¬ p6020))
    (h13116 : p3276 ∨ p6020)
    : p3276 ∨ (¬ p6019) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3276) := (fun h => hn (Or.inl h));
    let u1 : p6019 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6020) := (Or.elim h66580 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13116 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74359 (p3276 p4425 p6019 p6020 : Prop)
    (h66580 : (¬ p6019) ∨ (¬ p6020))
    (h13109 : p4425 ∨ p6019)
    (h9861 : (¬ p3276) ∨ (¬ p4425))
    : (¬ p3276) ∨ (¬ p6020) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3276 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6020 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6019) := (Or.elim h66580 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4425 := (Or.elim h13109 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9861 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74361 (p3309 p6022 p6023 : Prop)
    (h66581 : (¬ p6022) ∨ (¬ p6023))
    (h13135 : p3309 ∨ p6023)
    : p3309 ∨ (¬ p6022) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3309) := (fun h => hn (Or.inl h));
    let u1 : p6022 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6023) := (Or.elim h66581 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13135 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74363 (p3309 p3549 p6022 p6023 : Prop)
    (h66581 : (¬ p6022) ∨ (¬ p6023))
    (h13128 : p3549 ∨ p6022)
    (h9922 : (¬ p3309) ∨ (¬ p3549))
    : (¬ p3309) ∨ (¬ p6023) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3309 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6023 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6022) := (Or.elim h66581 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3549 := (Or.elim h13128 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9922 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74365 (p3319 p6025 p6026 : Prop)
    (h66582 : (¬ p6025) ∨ (¬ p6026))
    (h13152 : p3319 ∨ p6026)
    : p3319 ∨ (¬ p6025) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3319) := (fun h => hn (Or.inl h));
    let u1 : p6025 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6026) := (Or.elim h66582 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13152 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74367 (p3319 p4026 p6025 p6026 : Prop)
    (h66582 : (¬ p6025) ∨ (¬ p6026))
    (h13145 : p4026 ∨ p6025)
    (h9939 : (¬ p3319) ∨ (¬ p4026))
    : (¬ p3319) ∨ (¬ p6026) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3319 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6026 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6025) := (Or.elim h66582 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4026 := (Or.elim h13145 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9939 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74369 (p3343 p6031 p6032 : Prop)
    (h66584 : (¬ p6031) ∨ (¬ p6032))
    (h13187 : p3343 ∨ p6032)
    : p3343 ∨ (¬ p6031) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3343) := (fun h => hn (Or.inl h));
    let u1 : p6031 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6032) := (Or.elim h66584 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13187 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74371 (p3343 p3359 p6031 p6032 : Prop)
    (h66584 : (¬ p6031) ∨ (¬ p6032))
    (h13180 : p3359 ∨ p6031)
    (h11519 : (¬ p3343) ∨ (¬ p3359))
    : (¬ p3343) ∨ (¬ p6032) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6032 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6031) := (Or.elim h66584 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3359 := (Or.elim h13180 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11519 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74373 (p3379 p6037 p6038 : Prop)
    (h66586 : (¬ p6037) ∨ (¬ p6038))
    (h13227 : p3379 ∨ p6038)
    : p3379 ∨ (¬ p6037) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3379) := (fun h => hn (Or.inl h));
    let u1 : p6037 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6038) := (Or.elim h66586 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13227 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74375 (p3379 p3452 p6037 p6038 : Prop)
    (h66586 : (¬ p6037) ∨ (¬ p6038))
    (h13219 : p3452 ∨ p6037)
    (h10069 : (¬ p3379) ∨ (¬ p3452))
    : (¬ p3379) ∨ (¬ p6038) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3379 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6038 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6037) := (Or.elim h66586 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3452 := (Or.elim h13219 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10069 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74377 (p3389 p6040 p6041 : Prop)
    (h66587 : (¬ p6040) ∨ (¬ p6041))
    (h13244 : p3389 ∨ p6041)
    : p3389 ∨ (¬ p6040) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p6040 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6041) := (Or.elim h66587 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13244 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74379 (p3389 p3540 p6040 p6041 : Prop)
    (h66587 : (¬ p6040) ∨ (¬ p6041))
    (h13236 : p3540 ∨ p6040)
    (h9914 : (¬ p3389) ∨ (¬ p3540))
    : (¬ p3389) ∨ (¬ p6041) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6041 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6040) := (Or.elim h66587 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3540 := (Or.elim h13236 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9914 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74381 (p3399 p6043 p6044 : Prop)
    (h66588 : (¬ p6043) ∨ (¬ p6044))
    (h13260 : p3399 ∨ p6044)
    : p3399 ∨ (¬ p6043) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3399) := (fun h => hn (Or.inl h));
    let u1 : p6043 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6044) := (Or.elim h66588 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13260 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74383 (p3399 p4366 p6043 p6044 : Prop)
    (h66588 : (¬ p6043) ∨ (¬ p6044))
    (h13255 : p4366 ∨ p6043)
    (h9740 : (¬ p3399) ∨ (¬ p4366))
    : (¬ p3399) ∨ (¬ p6044) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3399 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6044 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6043) := (Or.elim h66588 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4366 := (Or.elim h13255 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9740 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74385 (p3367 p6046 p6047 : Prop)
    (h66589 : (¬ p6047) ∨ (¬ p6046))
    (h13280 : p3367 ∨ p6047)
    : p3367 ∨ (¬ p6046) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3367) := (fun h => hn (Or.inl h));
    let u1 : p6046 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6047) := (Or.elim h66589 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h13280 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74387 (p3367 p3585 p6046 p6047 : Prop)
    (h66589 : (¬ p6047) ∨ (¬ p6046))
    (h13273 : p3585 ∨ p6046)
    (h8999 : (¬ p3367) ∨ (¬ p3585))
    : (¬ p3367) ∨ (¬ p6047) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6047 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6046) := (Or.elim h66589 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3585 := (Or.elim h13273 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h8999 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74389 (p3422 p6049 p6050 : Prop)
    (h66590 : (¬ p6049) ∨ (¬ p6050))
    (h13298 : p3422 ∨ p6050)
    : p3422 ∨ (¬ p6049) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3422) := (fun h => hn (Or.inl h));
    let u1 : p6049 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6050) := (Or.elim h66590 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13298 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74391 (p3422 p3584 p6049 p6050 : Prop)
    (h66590 : (¬ p6049) ∨ (¬ p6050))
    (h13291 : p3584 ∨ p6049)
    (h9445 : (¬ p3422) ∨ (¬ p3584))
    : (¬ p3422) ∨ (¬ p6050) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3422 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6050 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6049) := (Or.elim h66590 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3584 := (Or.elim h13291 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9445 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74393 (p3434 p6052 p6053 : Prop)
    (h66591 : (¬ p6052) ∨ (¬ p6053))
    (h13318 : p3434 ∨ p6053)
    : p3434 ∨ (¬ p6052) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3434) := (fun h => hn (Or.inl h));
    let u1 : p6052 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6053) := (Or.elim h66591 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13318 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74395 (p3434 p4324 p6052 p6053 : Prop)
    (h66591 : (¬ p6052) ∨ (¬ p6053))
    (h13311 : p4324 ∨ p6052)
    (h10075 : (¬ p3434) ∨ (¬ p4324))
    : (¬ p3434) ∨ (¬ p6053) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3434 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6053 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6052) := (Or.elim h66591 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4324 := (Or.elim h13311 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10075 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74397 (p3449 p6055 p6056 : Prop)
    (h66592 : (¬ p6055) ∨ (¬ p6056))
    (h13339 : p3449 ∨ p6056)
    : p3449 ∨ (¬ p6055) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3449) := (fun h => hn (Or.inl h));
    let u1 : p6055 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6056) := (Or.elim h66592 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13339 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74399 (p3449 p3860 p6055 p6056 : Prop)
    (h66592 : (¬ p6055) ∨ (¬ p6056))
    (h13335 : p3860 ∨ p6055)
    (h10506 : (¬ p3449) ∨ (¬ p3860))
    : (¬ p3449) ∨ (¬ p6056) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3449 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6056 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6055) := (Or.elim h66592 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3860 := (Or.elim h13335 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10506 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74401 (p3461 p6058 p6059 : Prop)
    (h66593 : (¬ p6058) ∨ (¬ p6059))
    (h13361 : p3461 ∨ p6059)
    : p3461 ∨ (¬ p6058) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : p6058 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6059) := (Or.elim h66593 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13361 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74403 (p3461 p4191 p6058 p6059 : Prop)
    (h66593 : (¬ p6058) ∨ (¬ p6059))
    (h13354 : p4191 ∨ p6058)
    (h10619 : (¬ p3461) ∨ (¬ p4191))
    : (¬ p3461) ∨ (¬ p6059) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3461 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6059 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6058) := (Or.elim h66593 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4191 := (Or.elim h13354 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10619 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74405 (p3425 p3471 p6061 p6062 : Prop)
    (h66594 : (¬ p6061) ∨ (¬ p6062))
    (h13380 : p3471 ∨ p6062)
    (h9613 : (¬ p3425) ∨ (¬ p3471))
    : (¬ p3425) ∨ (¬ p6061) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3425 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6061 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6062) := (Or.elim h66594 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    let u3 : p3471 := (Or.elim h13380 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9613 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74407 (p3425 p6061 p6062 : Prop)
    (h66594 : (¬ p6061) ∨ (¬ p6062))
    (h13375 : p3425 ∨ p6061)
    : p3425 ∨ (¬ p6062) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3425) := (fun h => hn (Or.inl h));
    let u1 : p6062 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6061) := (Or.elim h66594 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h13375 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74409 (p3323 p6067 p6068 : Prop)
    (h66596 : (¬ p6067) ∨ (¬ p6068))
    (h13431 : p3323 ∨ p6068)
    : p3323 ∨ (¬ p6067) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p6067 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6068) := (Or.elim h66596 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13431 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74413 (p3516 p6073 p6074 : Prop)
    (h66598 : (¬ p6073) ∨ (¬ p6074))
    (h13476 : p3516 ∨ p6074)
    : p3516 ∨ (¬ p6073) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3516) := (fun h => hn (Or.inl h));
    let u1 : p6073 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6074) := (Or.elim h66598 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13476 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74415 (p3516 p3821 p6073 p6074 : Prop)
    (h66598 : (¬ p6073) ∨ (¬ p6074))
    (h13467 : p3821 ∨ p6073)
    (h10688 : (¬ p3516) ∨ (¬ p3821))
    : (¬ p3516) ∨ (¬ p6074) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3516 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6074 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6073) := (Or.elim h66598 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3821 := (Or.elim h13467 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10688 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74417 (p3527 p6076 p6077 : Prop)
    (h66599 : (¬ p6076) ∨ (¬ p6077))
    (h13492 : p3527 ∨ p6077)
    : p3527 ∨ (¬ p6076) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p6076 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6077) := (Or.elim h66599 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13492 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74419 (p3527 p3548 p6076 p6077 : Prop)
    (h66599 : (¬ p6076) ∨ (¬ p6077))
    (h13485 : p3548 ∨ p6076)
    (h9053 : (¬ p3527) ∨ (¬ p3548))
    : (¬ p3527) ∨ (¬ p6077) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3527 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6077 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6076) := (Or.elim h66599 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3548 := (Or.elim h13485 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9053 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74421 (p3537 p6079 p6080 : Prop)
    (h66600 : (¬ p6079) ∨ (¬ p6080))
    (h13513 : p3537 ∨ p6080)
    : p3537 ∨ (¬ p6079) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3537) := (fun h => hn (Or.inl h));
    let u1 : p6079 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6080) := (Or.elim h66600 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13513 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74423 (p3537 p4242 p6079 p6080 : Prop)
    (h66600 : (¬ p6079) ∨ (¬ p6080))
    (h13505 : p4242 ∨ p6079)
    (h10598 : (¬ p3537) ∨ (¬ p4242))
    : (¬ p3537) ∨ (¬ p6080) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3537 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6080 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6079) := (Or.elim h66600 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4242 := (Or.elim h13505 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10598 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74425 (p3564 p6082 p6083 : Prop)
    (h66601 : (¬ p6082) ∨ (¬ p6083))
    (h13551 : p3564 ∨ p6083)
    : p3564 ∨ (¬ p6082) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3564) := (fun h => hn (Or.inl h));
    let u1 : p6082 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6083) := (Or.elim h66601 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13551 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74427 (p3564 p4137 p6082 p6083 : Prop)
    (h66601 : (¬ p6082) ∨ (¬ p6083))
    (h13544 : p4137 ∨ p6082)
    (h9779 : (¬ p3564) ∨ (¬ p4137))
    : (¬ p3564) ∨ (¬ p6083) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6083 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6082) := (Or.elim h66601 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4137 := (Or.elim h13544 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9779 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74429 (p3599 p6085 p6086 : Prop)
    (h66602 : (¬ p6085) ∨ (¬ p6086))
    (h13624 : p3599 ∨ p6086)
    : p3599 ∨ (¬ p6085) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3599) := (fun h => hn (Or.inl h));
    let u1 : p6085 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6086) := (Or.elim h66602 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13624 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74431 (p3599 p4379 p6085 p6086 : Prop)
    (h66602 : (¬ p6085) ∨ (¬ p6086))
    (h13616 : p4379 ∨ p6085)
    (h11269 : (¬ p3599) ∨ (¬ p4379))
    : (¬ p3599) ∨ (¬ p6086) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3599 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6086 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6085) := (Or.elim h66602 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4379 := (Or.elim h13616 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11269 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74433 (p3609 p6088 p6089 : Prop)
    (h66603 : (¬ p6088) ∨ (¬ p6089))
    (h13640 : p3609 ∨ p6089)
    : p3609 ∨ (¬ p6088) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3609) := (fun h => hn (Or.inl h));
    let u1 : p6088 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6089) := (Or.elim h66603 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13640 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74435 (p3609 p4340 p6088 p6089 : Prop)
    (h66603 : (¬ p6088) ∨ (¬ p6089))
    (h13633 : p4340 ∨ p6088)
    (h10964 : (¬ p3609) ∨ (¬ p4340))
    : (¬ p3609) ∨ (¬ p6089) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3609 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6089 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6088) := (Or.elim h66603 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4340 := (Or.elim h13633 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10964 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74437 (p3631 p6094 p6095 : Prop)
    (h66605 : (¬ p6094) ∨ (¬ p6095))
    (h13675 : p3631 ∨ p6095)
    : p3631 ∨ (¬ p6094) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3631) := (fun h => hn (Or.inl h));
    let u1 : p6094 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6095) := (Or.elim h66605 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13675 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74439 (p3631 p3817 p6094 p6095 : Prop)
    (h66605 : (¬ p6094) ∨ (¬ p6095))
    (h13668 : p3817 ∨ p6094)
    (h10493 : (¬ p3631) ∨ (¬ p3817))
    : (¬ p3631) ∨ (¬ p6095) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3631 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6095 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6094) := (Or.elim h66605 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3817 := (Or.elim h13668 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10493 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74441 (p3641 p6097 p6098 : Prop)
    (h66606 : (¬ p6097) ∨ (¬ p6098))
    (h13705 : p3641 ∨ p6098)
    : p3641 ∨ (¬ p6097) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3641) := (fun h => hn (Or.inl h));
    let u1 : p6097 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6098) := (Or.elim h66606 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13705 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74443 (p3641 p3874 p6097 p6098 : Prop)
    (h66606 : (¬ p6097) ∨ (¬ p6098))
    (h13698 : p3874 ∨ p6097)
    (h11620 : (¬ p3641) ∨ (¬ p3874))
    : (¬ p3641) ∨ (¬ p6098) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3641 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6098 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6097) := (Or.elim h66606 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3874 := (Or.elim h13698 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11620 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74445 (p3654 p6100 p6101 : Prop)
    (h66607 : (¬ p6100) ∨ (¬ p6101))
    (h13738 : p3654 ∨ p6101)
    : p3654 ∨ (¬ p6100) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p6100 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6101) := (Or.elim h66607 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13738 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74447 (p3654 p3946 p6100 p6101 : Prop)
    (h66607 : (¬ p6100) ∨ (¬ p6101))
    (h13730 : p3946 ∨ p6100)
    (h9737 : (¬ p3654) ∨ (¬ p3946))
    : (¬ p3654) ∨ (¬ p6101) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6101 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6100) := (Or.elim h66607 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3946 := (Or.elim h13730 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9737 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74449 (p3670 p6103 p6104 : Prop)
    (h66608 : (¬ p6103) ∨ (¬ p6104))
    (h13772 : p3670 ∨ p6104)
    : p3670 ∨ (¬ p6103) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3670) := (fun h => hn (Or.inl h));
    let u1 : p6103 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6104) := (Or.elim h66608 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13772 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74451 (p3670 p5387 p6103 p6104 : Prop)
    (h66608 : (¬ p6103) ∨ (¬ p6104))
    (h13765 : p5387 ∨ p6103)
    (h11268 : (¬ p3670) ∨ (¬ p5387))
    : (¬ p3670) ∨ (¬ p6104) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3670 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6104 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6103) := (Or.elim h66608 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p5387 := (Or.elim h13765 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11268 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74455 (p3707 p4321 p6109 p6110 : Prop)
    (h66610 : (¬ p6109) ∨ (¬ p6110))
    (h13827 : p4321 ∨ p6109)
    (h9574 : (¬ p3707) ∨ (¬ p4321))
    : (¬ p3707) ∨ (¬ p6110) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3707 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6110 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6109) := (Or.elim h66610 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4321 := (Or.elim h13827 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h9574 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74457 (p3755 p6121 p6122 : Prop)
    (h66614 : (¬ p6121) ∨ (¬ p6122))
    (h13921 : p3755 ∨ p6122)
    : p3755 ∨ (¬ p6121) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3755) := (fun h => hn (Or.inl h));
    let u1 : p6121 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6122) := (Or.elim h66614 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h13921 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74459 (p3755 p4035 p6121 p6122 : Prop)
    (h66614 : (¬ p6121) ∨ (¬ p6122))
    (h13914 : p4035 ∨ p6121)
    (h11173 : (¬ p3755) ∨ (¬ p4035))
    : (¬ p3755) ∨ (¬ p6122) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3755 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6122 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6121) := (Or.elim h66614 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4035 := (Or.elim h13914 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11173 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74461 (p3830 p6127 p6128 : Prop)
    (h66616 : (¬ p6127) ∨ (¬ p6128))
    (h14012 : p3830 ∨ p6128)
    : p3830 ∨ (¬ p6127) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3830) := (fun h => hn (Or.inl h));
    let u1 : p6127 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6128) := (Or.elim h66616 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h14012 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74463 (p3830 p3834 p6127 p6128 : Prop)
    (h66616 : (¬ p6127) ∨ (¬ p6128))
    (h14008 : p3834 ∨ p6127)
    (h11298 : (¬ p3830) ∨ (¬ p3834))
    : (¬ p3830) ∨ (¬ p6128) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3830 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6128 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6127) := (Or.elim h66616 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p3834 := (Or.elim h14008 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h11298 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74465 (p4149 p6175 p6176 : Prop)
    (h66632 : (¬ p6175) ∨ (¬ p6176))
    (h15088 : p4149 ∨ p6176)
    : p4149 ∨ (¬ p6175) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p6175 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6176) := (Or.elim h66632 (fun q0 => (False.elim (q0 u1))) (fun r0 => r0));
    (Or.elim h15088 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (u2 r0)))))

theorem step74467 (p4149 p4286 p6175 p6176 : Prop)
    (h66632 : (¬ p6175) ∨ (¬ p6176))
    (h15081 : p4286 ∨ p6175)
    (h10735 : (¬ p4149) ∨ (¬ p4286))
    : (¬ p4149) ∨ (¬ p6176) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4149 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p6176 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : (¬ p6175) := (Or.elim h66632 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    let u3 : p4286 := (Or.elim h15081 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h10735 (fun q0 => (False.elim (q0 u0))) (fun r0 => (False.elim (r0 u3)))))

theorem step74469 (p2363 p2528 p4347 p4432 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h20214 : (¬ p2528) ∨ (¬ p4347) ∨ (¬ p4432))
    : (¬ p2528) ∨ p2363 ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2363) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h20214 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step74474 (p2274 p2363 p2528 p2553 p2588 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73282 : p2588 ∨ p2553)
    (h67232 : (¬ p2588) ∨ (¬ p4347) ∨ (¬ p2274) ∨ (¬ p2528))
    : (¬ p2528) ∨ (¬ p2274) ∨ p2363 ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2528 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2363) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h67232 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74475 (p2440 p4241 p4703 : Prop)
    (h73714 : p4703 ∨ p2440)
    (h7588 : p4241 ∨ (¬ p4703))
    : p4241 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4241) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr h));
    let u2 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h7588 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step74477 (p2440 p4703 p4705 : Prop)
    (h73714 : p4703 ∨ p2440)
    (h7592 : (¬ p4703) ∨ p4705)
    : p2440 ∨ p4705 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4705) := (fun h => hn (Or.inr h));
    let u2 : p4703 := (Or.elim h73714 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h7592 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74478 (p2363 p2459 p3550 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h18858 : (¬ p2459) ∨ (¬ p3550) ∨ (¬ p4347))
    : p2363 ∨ (¬ p3550) ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h18858 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step74486 (p2459 p4348 p4668 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h42873 : (¬ p4348) ∨ p4668)
    : p2459 ∨ p4668 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4668) := (fun h => hn (Or.inr h));
    let u2 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42873 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74488 (p2459 p4348 p4669 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h49219 : (¬ p4348) ∨ p4669)
    : p2459 ∨ p4669 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4669) := (fun h => hn (Or.inr h));
    let u2 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h49219 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74491 (p2427 p2440 p2459 p2881 p3570 p4235 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73536 : p4235 ∨ p2427)
    (h51443 : (¬ p2440) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ (¬ p2440) ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h51443 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74492 (p2427 p2459 p2850 p2881 p3570 p3684 p4235 p4348 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h73536 : p4235 ∨ p2427)
    (h73442 : p3684 ∨ p2850)
    (h44133 : (¬ p3570) ∨ (¬ p3684) ∨ (¬ p4235) ∨ (¬ p4348))
    : p2881 ∨ p2459 ∨ p2427 ∨ p2850 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2850) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3684 := (Or.elim h73442 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44133 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74493 (p2427 p2459 p2881 p3266 p3570 p4235 p4348 p4444 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73580 : p4444 ∨ p3266)
    (h73536 : p4235 ∨ p2427)
    (h45454 : (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348) ∨ (¬ p4444))
    : p2459 ∨ p2881 ∨ p3266 ∨ p2427 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3266) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4444 := (Or.elim h73580 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45454 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step74494 (p2427 p2459 p2563 p2881 p3570 p4235 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73536 : p4235 ∨ p2427)
    (h46400 : (¬ p2563) ∨ (¬ p3570) ∨ (¬ p4235) ∨ (¬ p4348))
    : p2459 ∨ p2881 ∨ p2427 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2427) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46400 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74495 (p2210 p2459 p2881 p2891 p3486 p3555 p3570 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73418 : p3570 ∨ p2881)
    (h73412 : p3555 ∨ p2210)
    (h73398 : p3486 ∨ p2891)
    (h43355 : (¬ p3486) ∨ (¬ p3555) ∨ (¬ p3570) ∨ (¬ p4348))
    : p2459 ∨ p2881 ∨ p2210 ∨ p2891 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2881) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2210) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2891) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3555 := (Or.elim h73412 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3486 := (Or.elim h73398 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43355 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74497 (p2177 p2299 p2459 p2573 p3389 p3540 p3921 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73402 : p3540 ∨ p3389)
    (h47464 : (¬ p2299) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p4348))
    : p2459 ∨ p2177 ∨ p3389 ∨ (¬ p3921) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3389) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47464 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step74499 (p2459 p2528 p2534 p4348 p4383 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73267 : (¬ p2528) ∨ (¬ p2534))
    (h39893 : p2534 ∨ (¬ p4348) ∨ (¬ p4383))
    : (¬ p4383) ∨ p2459 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4383 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p2534) := (Or.elim h73267 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h39893 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step74502 (p2177 p2459 p2528 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h67131 : p2177 ∨ (¬ p4348) ∨ (¬ p2528))
    : p2459 ∨ p2177 ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h67131 (fun q0 => (False.elim (u1 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u2)))))))

theorem step74503 (p2459 p2528 p2881 p3570 p3875 p4348 p4647 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73562 : p4348 ∨ p2459)
    (h40940 : (¬ p2528) ∨ (¬ p3570) ∨ (¬ p3875) ∨ (¬ p4348) ∨ (¬ p4647))
    : p2881 ∨ p2459 ∨ (¬ p2528) ∨ (¬ p3875) ∨ (¬ p4647) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3875 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4647 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h40940 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74504 (p2241 p2459 p2641 p2881 p3051 p3323 p3556 p3570 p4330 p4348 p4524 : Prop)
    (h72962 : p4524)
    (h73418 : p3570 ∨ p2881)
    (h73414 : p3556 ∨ p3051)
    (h73562 : p4348 ∨ p2459)
    (h64104 : (¬ p2241) ∨ (¬ p2641) ∨ (¬ p3323) ∨ (¬ p3556) ∨ (¬ p3570) ∨ (¬ p4330) ∨ (¬ p4348) ∨ (¬ p4524))
    : (¬ p3323) ∨ (¬ p2241) ∨ p2881 ∨ (¬ p2641) ∨ p3051 ∨ (¬ p4330) ∨ p2459 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3323 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2641 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3051) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4330 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p4524 := h72962;
    let u8 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p3556 := (Or.elim h73414 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u10 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h64104 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u9))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u8))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u5))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u7)))))))))))))))))

theorem step74505 (p2177 p2274 p2299 p2459 p2563 p3097 p4110 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73352 : p3097 ∨ p2274)
    (h73516 : p4110 ∨ p2563)
    (h42811 : (¬ p2299) ∨ (¬ p3097) ∨ (¬ p4110) ∨ (¬ p4348))
    : p2459 ∨ p2177 ∨ p2274 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42811 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74506 (p2177 p2299 p2437 p2459 p3016 p3742 p3921 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73234 : p2299 ∨ p2177)
    (h73452 : p3742 ∨ p2437)
    (h63780 : (¬ p2299) ∨ (¬ p3016) ∨ (¬ p3742) ∨ (¬ p3921) ∨ (¬ p4348))
    : p2459 ∨ p2177 ∨ (¬ p3016) ∨ (¬ p3921) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2459) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2177) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h63780 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step74507 (p2177 p2299 p2459 p2553 p2588 p3422 p3584 p4348 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73282 : p2588 ∨ p2553)
    (h73562 : p4348 ∨ p2459)
    (h73426 : p3584 ∨ p3422)
    (h46427 : (¬ p2299) ∨ (¬ p2588) ∨ (¬ p3584) ∨ (¬ p4348))
    : p2177 ∨ p2553 ∨ p2459 ∨ p3422 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2177) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2553) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3422) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3584 := (Or.elim h73426 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46427 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step74509 (p2440 p2542 p4753 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h42889 : (¬ p2542) ∨ p4753)
    : p2440 ∨ p4753 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4753) := (fun h => hn (Or.inr h));
    let u2 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h42889 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74510 (p2440 p2542 p4717 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h47203 : (¬ p2542) ∨ p4717)
    : p2440 ∨ p4717 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p4717) := (fun h => hn (Or.inr h));
    let u2 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47203 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74512 (p2440 p2542 p3016 p3564 p3574 p3654 p4137 : Prop)
    (h73524 : p4137 ∨ p3564)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h47268 : (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3654) ∨ (¬ p4137))
    : (¬ p3654) ∨ p3564 ∨ p3016 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3654 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3564) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47268 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74513 (p2230 p2440 p2542 p2553 p2573 p2589 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h42654 : (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589))
    : p2440 ∨ (¬ p2553) ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42654 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74515 (p2284 p2440 p2542 p2563 p2651 p3952 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73496 : p3952 ∨ p2284)
    (h52511 : (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651) ∨ (¬ p3952))
    : p2440 ∨ (¬ p2651) ∨ (¬ p2563) ∨ p2284 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2651 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2284) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52511 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74516 (p2241 p2440 p2542 p2563 p2727 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h43376 : (¬ p2241) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2727))
    : (¬ p2727) ∨ (¬ p2241) ∨ (¬ p2563) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2727 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2241 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43376 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74518 (p2440 p2470 p2542 p2563 p3083 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h46975 : (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p4256))
    : (¬ p2470) ∨ p3083 ∨ p2440 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46975 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74520 (p2230 p2440 p2542 p2589 p2662 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h6146 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2662))
    : p2440 ∨ (¬ p2662) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h6146 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (False.elim (r1 u1)))))))

theorem step74522 (p2230 p2440 p2542 p2573 p2589 p2630 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h44857 : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2630))
    : p2440 ∨ (¬ p2630) ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44857 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74523 (p2177 p2299 p2440 p2470 p2542 p2563 p3083 p3093 p3309 p3549 p3591 p4256 p5190 : Prop)
    (h73432 : p3591 ∨ p3093)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h73234 : p2299 ∨ p2177)
    (h73406 : p3549 ∨ p3309)
    (h53337 : (¬ p2299) ∨ (¬ p2470) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p3549) ∨ (¬ p3591) ∨ (¬ p4256) ∨ (¬ p5190))
    : p3093 ∨ p3083 ∨ (¬ p2563) ∨ (¬ p2470) ∨ p2440 ∨ (¬ p5190) ∨ p2177 ∨ p3309 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3093) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2470 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p5190 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : (¬ p3309) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p3591 := (Or.elim h73432 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u10 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    let u12 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u7 r0))));
    (Or.elim h53337 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u10))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u12))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u9))) (fun r6 => (False.elim (r6 u5)))))))))))))))))

theorem step74528 (p2230 p2440 p2542 p2589 p2630 p2655 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h71238 : (¬ p2542) ∨ (¬ p2630) ∨ (¬ p2655) ∨ (¬ p2589))
    : p2440 ∨ (¬ p2655) ∨ p2230 ∨ (¬ p2630) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71238 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74532 (p2230 p2437 p2440 p2542 p2589 p2911 p3644 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h73434 : p3644 ∨ p2911)
    (h53117 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3644) ∨ (¬ p3742))
    : p2437 ∨ p2440 ∨ p2230 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2437) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53117 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74533 (p2437 p2440 p2470 p2476 p2542 p3389 p3742 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h73250 : p2476 ∨ p2470)
    (h54151 : (¬ p2476) ∨ (¬ p2542) ∨ (¬ p3389) ∨ (¬ p3742))
    : (¬ p3389) ∨ p2440 ∨ p2437 ∨ p2470 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54151 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74534 (p2230 p2440 p2542 p2589 p2655 p3166 p3189 p4360 : Prop)
    (h73566 : p4360 ∨ p3189)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h55685 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p3166) ∨ (¬ p4360))
    : (¬ p3166) ∨ p3189 ∨ p2440 ∨ (¬ p2655) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3166 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3189) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4360 := (Or.elim h73566 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h55685 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step74535 (p2341 p2437 p2440 p2542 p2881 p3551 p3742 p4279 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h59064 : (¬ p2542) ∨ (¬ p2881) ∨ (¬ p3551) ∨ (¬ p3742) ∨ (¬ p4279))
    : p2341 ∨ (¬ p4279) ∨ p2437 ∨ (¬ p2881) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2341) := (fun h => hn (Or.inl h));
    let u1 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h59064 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74536 (p2230 p2440 p2542 p2589 p2881 p3389 p3569 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h51993 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p3569))
    : (¬ p3389) ∨ p2440 ∨ (¬ p3569) ∨ (¬ p2881) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h51993 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74537 (p2427 p2440 p2459 p2542 p2881 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h47255 : (¬ p2427) ∨ (¬ p2459) ∨ (¬ p2542) ∨ (¬ p2881))
    : (¬ p2881) ∨ (¬ p2427) ∨ p2440 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2881 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2427 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h47255 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74541 (p2230 p2440 p2528 p2534 p2542 p2589 p2655 p3083 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h46836 : (¬ p2534) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p4256))
    : p2528 ∨ p3083 ∨ p2440 ∨ (¬ p2655) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46836 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u8))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step74543 (p2230 p2440 p2542 p2589 p3343 p3359 p4322 p4947 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h45642 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3359) ∨ (¬ p4322) ∨ (¬ p4947))
    : (¬ p4322) ∨ p3343 ∨ p2440 ∨ p2230 ∨ (¬ p4947) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4322 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4947 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45642 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74546 (p2440 p2542 p2662 p3276 p3773 p4949 p5181 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h60745 : (¬ p2542) ∨ (¬ p2662) ∨ (¬ p3276) ∨ (¬ p3773) ∨ (¬ p4949) ∨ (¬ p5181))
    : (¬ p3773) ∨ (¬ p3276) ∨ p2440 ∨ (¬ p2662) ∨ (¬ p5181) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3773 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60745 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step74547 (p2440 p2542 p3276 p4949 p5170 p5284 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h42010 : (¬ p2542) ∨ (¬ p3276) ∨ (¬ p4949) ∨ (¬ p5170) ∨ (¬ p5284))
    : (¬ p5284) ∨ (¬ p3276) ∨ p2440 ∨ (¬ p5170) ∨ (¬ p4949) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5170 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4949 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42010 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step74549 (p2230 p2440 p2542 p2589 p2655 p2807 p4652 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h53648 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652))
    : p2440 ∨ (¬ p2655) ∨ (¬ p2807) ∨ (¬ p4652) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2655 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4652 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53648 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74550 (p2396 p2437 p2440 p2542 p3246 p3690 p3742 p4001 : Prop)
    (h73446 : p3690 ∨ p3246)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h48760 : (¬ p2396) ∨ (¬ p2542) ∨ (¬ p3690) ∨ (¬ p3742) ∨ (¬ p4001))
    : p3246 ∨ (¬ p4001) ∨ (¬ p2396) ∨ p2440 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3246) := (fun h => hn (Or.inl h));
    let u1 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2396 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3690 := (Or.elim h73446 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h48760 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74551 (p2274 p2396 p2440 p2542 p2563 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h53679 : (¬ p2274) ∨ (¬ p2396) ∨ (¬ p2542) ∨ (¬ p2563))
    : (¬ p2396) ∨ (¬ p2274) ∨ p2440 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2396 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53679 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step74553 (p2230 p2417 p2437 p2440 p2542 p2589 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73452 : p3742 ∨ p2437)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h46895 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ p2437 ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46895 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74555 (p2417 p2440 p2449 p2542 p3947 p4112 p4644 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73270 : p2542 ∨ p2440)
    (h52210 : (¬ p2417) ∨ (¬ p2542) ∨ (¬ p3947) ∨ (¬ p4112) ∨ (¬ p4644))
    : p2449 ∨ (¬ p2417) ∨ (¬ p4112) ∨ p2440 ∨ (¬ p4644) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2449) := (fun h => hn (Or.inl h));
    let u1 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h52210 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74558 (p2437 p2440 p2459 p2542 p2911 p3644 p3742 p4348 : Prop)
    (h73434 : p3644 ∨ p2911)
    (h73562 : p4348 ∨ p2459)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h46011 : (¬ p2542) ∨ (¬ p3644) ∨ (¬ p3742) ∨ (¬ p4348))
    : p2911 ∨ p2459 ∨ p2440 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2911) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2459) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46011 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74559 (p2341 p2437 p2440 p2542 p2911 p3644 p3742 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h73434 : p3644 ∨ p2911)
    (h46947 : (¬ p2341) ∨ (¬ p2542) ∨ (¬ p3644) ∨ (¬ p3742))
    : (¬ p2341) ∨ p2437 ∨ p2440 ∨ p2911 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2341 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2911) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3644 := (Or.elim h73434 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46947 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74563 (p2440 p2528 p2542 p3256 p4118 p4608 : Prop)
    (h73520 : p4118 ∨ p3256)
    (h73270 : p2542 ∨ p2440)
    (h66814 : (¬ p2528) ∨ (¬ p2542) ∨ (¬ p4118) ∨ (¬ p4608))
    : p3256 ∨ (¬ p2528) ∨ p2440 ∨ (¬ p4608) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3256) := (fun h => hn (Or.inl h));
    let u1 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4118 := (Or.elim h73520 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h66814 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step74565 (p2264 p2440 p2542 p2911 p3553 p4112 p4644 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73410 : p3553 ∨ p2264)
    (h62777 : (¬ p2542) ∨ (¬ p2911) ∨ (¬ p3553) ∨ (¬ p4112) ∨ (¬ p4644))
    : (¬ p2911) ∨ p2440 ∨ p2264 ∨ (¬ p4644) ∨ (¬ p4112) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62777 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74568 (p2440 p2542 p2573 p3016 p3346 p3574 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h58701 : (¬ p2542) ∨ (¬ p2573) ∨ (¬ p3346) ∨ (¬ p3574))
    : (¬ p3346) ∨ p3016 ∨ (¬ p2573) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58701 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74572 (p2352 p2440 p2542 p2668 p3324 p4194 p4715 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73386 : p3324 ∨ p2668)
    (h58925 : (¬ p2352) ∨ (¬ p2542) ∨ (¬ p3324) ∨ (¬ p4194) ∨ (¬ p4715))
    : (¬ p2352) ∨ (¬ p4194) ∨ p2440 ∨ p2668 ∨ (¬ p4715) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2668) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3324 := (Or.elim h73386 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h58925 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74573 (p2440 p2459 p2528 p2534 p2542 p3083 p4256 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h53443 : (¬ p2459) ∨ (¬ p2534) ∨ (¬ p2542) ∨ (¬ p4256))
    : p2528 ∨ p3083 ∨ p2440 ∨ (¬ p2459) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2459 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h53443 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74574 (p2440 p2542 p3323 p3564 p4037 p4194 p4715 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73270 : p2542 ∨ p2440)
    (h49914 : (¬ p2542) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4194) ∨ (¬ p4715))
    : (¬ p3564) ∨ p3323 ∨ (¬ p4715) ∨ p2440 ∨ (¬ p4194) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3323) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49914 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74576 (p2440 p2542 p3323 p3422 p3564 p4037 p4194 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73508 : p4037 ∨ p3323)
    (h46627 : (¬ p2542) ∨ (¬ p3422) ∨ (¬ p3564) ∨ (¬ p4037) ∨ (¬ p4194))
    : (¬ p3564) ∨ (¬ p3422) ∨ (¬ p4194) ∨ p2440 ∨ p3323 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3323) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h46627 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74578 (p2417 p2437 p2440 p2542 p3246 p3742 p4278 : Prop)
    (h73546 : p4278 ∨ p2417)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h42971 : (¬ p2542) ∨ (¬ p3246) ∨ (¬ p3742) ∨ (¬ p4278))
    : p2417 ∨ (¬ p3246) ∨ p2440 ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2417) := (fun h => hn (Or.inl h));
    let u1 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4278 := (Or.elim h73546 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42971 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74581 (p2230 p2295 p2440 p2542 p2553 p2589 p3568 p4194 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h44453 : (¬ p2542) ∨ (¬ p2553) ∨ (¬ p2589) ∨ (¬ p3568) ∨ (¬ p4194))
    : p2295 ∨ p2440 ∨ (¬ p2553) ∨ (¬ p4194) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4194 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h44453 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74584 (p2440 p2542 p2881 p3246 p3343 p3359 p3570 p4636 : Prop)
    (h73388 : p3359 ∨ p3343)
    (h73418 : p3570 ∨ p2881)
    (h73270 : p2542 ∨ p2440)
    (h60507 : (¬ p2542) ∨ (¬ p3246) ∨ (¬ p3359) ∨ (¬ p3570) ∨ (¬ p4636))
    : (¬ p4636) ∨ p3343 ∨ p2881 ∨ p2440 ∨ (¬ p3246) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4636 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3343) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3246 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3359 := (Or.elim h73388 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h60507 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step74585 (p2156 p2440 p2542 p3016 p3096 p3574 p4539 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h51992 : (¬ p2156) ∨ (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3574) ∨ (¬ p4539))
    : p2440 ∨ p3016 ∨ (¬ p4539) ∨ (¬ p3096) ∨ (¬ p2156) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2156 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h51992 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74586 (p2341 p2440 p2542 p2911 p3551 p4112 p4155 p4644 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73408 : p3551 ∨ p2341)
    (h62778 : (¬ p2542) ∨ (¬ p2911) ∨ (¬ p3551) ∨ (¬ p4112) ∨ (¬ p4155) ∨ (¬ p4644))
    : (¬ p4112) ∨ p2440 ∨ (¬ p4155) ∨ p2341 ∨ (¬ p4644) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4112 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4155 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4644 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62778 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u2))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step74588 (p2274 p2406 p2440 p2542 p3016 p3096 p3097 p3238 p3402 p3574 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73422 : p3574 ∨ p3016)
    (h73374 : p3238 ∨ p2406)
    (h73270 : p2542 ∨ p2440)
    (h49362 : (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3097) ∨ (¬ p3238) ∨ (¬ p3402) ∨ (¬ p3574))
    : (¬ p3402) ∨ p2274 ∨ p3016 ∨ (¬ p3096) ∨ p2406 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3402 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3016) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u9 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u5 r0))));
    (Or.elim h49362 (fun q0 => (False.elim (q0 u9))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u8))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u0))) (fun r4 => (False.elim (r4 u7)))))))))))))

theorem step74589 (p2187 p2406 p2440 p2542 p3016 p3096 p3238 p3574 p3989 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73422 : p3574 ∨ p3016)
    (h73374 : p3238 ∨ p2406)
    (h73502 : p3989 ∨ p2187)
    (h44325 : (¬ p2542) ∨ (¬ p3096) ∨ (¬ p3238) ∨ (¬ p3574) ∨ (¬ p3989))
    : p2440 ∨ p3016 ∨ p2406 ∨ p2187 ∨ (¬ p3096) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3096 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44325 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u8)))))))))))

theorem step74591 (p2177 p2274 p2440 p2542 p2563 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h62177 : (¬ p2177) ∨ (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2563))
    : (¬ p2274) ∨ (¬ p2177) ∨ p2440 ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2274 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62177 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step74592 (p2274 p2440 p2542 p2563 p2651 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h43072 : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2563) ∨ (¬ p2651))
    : (¬ p2651) ∨ p2440 ∨ (¬ p2274) ∨ (¬ p2563) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2651 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2563 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43072 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74593 (p2230 p2274 p2437 p2440 p2542 p2589 p3742 p3921 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73284 : p2589 ∨ p2230)
    (h73270 : p2542 ∨ p2440)
    (h53213 : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3742) ∨ (¬ p3921))
    : (¬ p3921) ∨ (¬ p2274) ∨ p2437 ∨ p2230 ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3921 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53213 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step74596 (p2187 p2274 p2307 p2313 p2363 p2440 p2542 p2630 p2696 p2787 p3989 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73238 : p2313 ∨ p2307)
    (h73502 : p3989 ∨ p2187)
    (h73270 : p2542 ∨ p2440)
    (h48978 : (¬ p2274) ∨ (¬ p2313) ∨ (¬ p2542) ∨ (¬ p2630) ∨ (¬ p2696) ∨ (¬ p2787) ∨ (¬ p3989) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2630) ∨ p2307 ∨ (¬ p2274) ∨ p2187 ∨ (¬ p2696) ∨ p2440 ∨ (¬ p2787) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2630 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2307) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2696 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))));
    let u8 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u9 : p2313 := (Or.elim h73238 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u10 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h48978 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (False.elim (r6 u8)))))))))))))))))

theorem step74597 (p2187 p2352 p2440 p2542 p3016 p3574 p3956 : Prop)
    (h73422 : p3574 ∨ p3016)
    (h73270 : p2542 ∨ p2440)
    (h73500 : p3956 ∨ p2352)
    (h47716 : (¬ p2187) ∨ (¬ p2542) ∨ (¬ p3574) ∨ (¬ p3956))
    : (¬ p2187) ∨ p3016 ∨ p2440 ∨ p2352 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2187 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3016) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3574 := (Or.elim h73422 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47716 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step74598 (p2177 p2437 p2440 p2542 p2881 p3570 p3742 p4001 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h61246 : (¬ p2177) ∨ (¬ p2542) ∨ (¬ p3570) ∨ (¬ p3742) ∨ (¬ p4001))
    : p2881 ∨ (¬ p2177) ∨ p2437 ∨ (¬ p4001) ∨ p2440 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2881) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4001 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h61246 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74600 (p2274 p2440 p2542 p2553 p2573 p2579 p2588 p2662 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73282 : p2588 ∨ p2553)
    (h73274 : p2579 ∨ p2573)
    (h45495 : (¬ p2274) ∨ (¬ p2542) ∨ (¬ p2579) ∨ (¬ p2588) ∨ (¬ p2662))
    : p2440 ∨ (¬ p2662) ∨ p2553 ∨ p2573 ∨ (¬ p2274) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : p2662 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45495 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74604 (p2187 p2319 p2437 p2440 p2542 p3125 p3654 p3742 p3946 p3989 p4279 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h73502 : p3989 ∨ p2187)
    (h73270 : p2542 ∨ p2440)
    (h73452 : p3742 ∨ p2437)
    (h57640 : (¬ p2319) ∨ (¬ p2542) ∨ (¬ p3125) ∨ (¬ p3742) ∨ (¬ p3946) ∨ (¬ p3989) ∨ (¬ p4279))
    : p3654 ∨ (¬ p3125) ∨ p2187 ∨ p2440 ∨ (¬ p4279) ∨ (¬ p2319) ∨ p2437 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3654) := (fun h => hn (Or.inl h));
    let u1 : p3125 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4279 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2319 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))));
    let u7 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u8 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u9 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u10 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u6 r0))));
    (Or.elim h57640 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u10))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u7))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u8))) (fun r5 => (False.elim (r5 u4)))))))))))))))

theorem step74607 (p2177 p3550 p4502 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h7060 : p3550 ∨ (¬ p4502))
    : p3550 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3550) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7060 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step74609 (p2177 p4405 p4502 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h7063 : p4405 ∨ (¬ p4502))
    : p4405 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4405) := (fun h => hn (Or.inl h));
    let u1 : p2177 := Classical.byContradiction (fun h => hn (Or.inr h));
    let u2 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h7063 (fun q0 => (False.elim (u0 q0))) (fun r0 => (False.elim (r0 u2)))))

theorem step74610 (p2177 p4502 p4503 : Prop)
    (h73604 : p4502 ∨ (¬ p2177))
    (h7064 : (¬ p4502) ∨ p4503)
    : (¬ p2177) ∨ p4503 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2177 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p4503) := (fun h => hn (Or.inr h));
    let u2 : p4502 := (Or.elim h73604 (fun q0 => q0) (fun r0 => (False.elim (r0 u0))));
    (Or.elim h7064 (fun q0 => (False.elim (q0 u2))) (fun r0 => (False.elim (u1 r0)))))

theorem step74611 (p2187 p2274 p3097 p3550 p4260 p5559 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h50265 : (¬ p2187) ∨ (¬ p3097) ∨ (¬ p3550) ∨ (¬ p4260) ∨ (¬ p5559))
    : (¬ p4260) ∨ p2274 ∨ (¬ p2187) ∨ (¬ p5559) ∨ (¬ p3550) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4260 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3550 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50265 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74612 (p2088 p2459 p4066 p4348 p4391 p4590 p5559 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h60811 : (¬ p2088) ∨ (¬ p4066) ∨ (¬ p4348) ∨ (¬ p4391) ∨ (¬ p4590) ∨ (¬ p5559))
    : (¬ p4066) ∨ (¬ p4391) ∨ (¬ p5559) ∨ (¬ p4590) ∨ p2459 ∨ (¬ p2088) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4066 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4391 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5559 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2088 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h60811 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step74622 (p2510 p3016 p3083 p3574 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73421 : (¬ p3016) ∨ (¬ p3574))
    (h28103 : (¬ p2510) ∨ p3574 ∨ (¬ p4256))
    : (¬ p2510) ∨ p3083 ∨ (¬ p3016) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3574) := (Or.elim h73421 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h28103 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (u4 q1))) (fun r1 => (False.elim (r1 u3)))))))

theorem step74627 (p2437 p3083 p3742 p3875 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73451 : (¬ p2437) ∨ (¬ p3742))
    (h6707 : p3742 ∨ (¬ p3875) ∨ (¬ p4256))
    : (¬ p3875) ∨ p3083 ∨ (¬ p2437) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3875 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u4 : (¬ p3742) := (Or.elim h73451 (fun q0 => (False.elim (q0 u2))) (fun r0 => r0));
    (Or.elim h6707 (fun q0 => (False.elim (u4 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u3)))))))

theorem step74631 (p2459 p3083 p3343 p4256 p4348 p4438 p4695 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h73542 : p4256 ∨ p3083)
    (h48106 : (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4348) ∨ (¬ p4438) ∨ (¬ p4695))
    : (¬ p3343) ∨ (¬ p4438) ∨ p2459 ∨ p3083 ∨ (¬ p4695) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3343 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4438 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48106 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74633 (p2156 p2284 p3083 p3413 p3646 p4031 p4256 p4608 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73436 : p3646 ∨ p2156)
    (h42162 : (¬ p2284) ∨ (¬ p3413) ∨ (¬ p3646) ∨ (¬ p4031) ∨ (¬ p4256) ∨ (¬ p4608))
    : (¬ p2284) ∨ (¬ p4031) ∨ p3083 ∨ p2156 ∨ (¬ p4608) ∨ (¬ p3413) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2284 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4031 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2156) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4608 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3413 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p3646 := (Or.elim h73436 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42162 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step74635 (p2470 p2476 p2656 p3083 p4256 : Prop)
    (h73249 : (¬ p2470) ∨ (¬ p2476))
    (h73542 : p4256 ∨ p3083)
    (h6706 : p2476 ∨ (¬ p2656) ∨ (¬ p4256))
    : (¬ p2470) ∨ p3083 ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : (¬ p2476) := (Or.elim h73249 (fun q0 => (False.elim (q0 u0))) (fun r0 => r0));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h6706 (fun q0 => (False.elim (u3 q0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u4)))))))

theorem step74642 (p2437 p2470 p2911 p3083 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h47516 : (¬ p2437) ∨ (¬ p2470) ∨ (¬ p2911) ∨ (¬ p4256))
    : (¬ p2470) ∨ (¬ p2911) ∨ (¬ p2437) ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47516 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74643 (p2470 p2553 p2663 p3016 p3083 p4256 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h43783 : (¬ p2470) ∨ (¬ p2553) ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p4256))
    : (¬ p2470) ∨ p3083 ∨ (¬ p2663) ∨ (¬ p3016) ∨ (¬ p2553) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2470 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2663 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h43783 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step74644 (p2363 p2656 p3083 p3355 p4256 p4347 p4384 p4695 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73542 : p4256 ∨ p3083)
    (h48186 : (¬ p2656) ∨ (¬ p3355) ∨ (¬ p4256) ∨ (¬ p4347) ∨ (¬ p4384) ∨ (¬ p4695))
    : p2363 ∨ (¬ p3355) ∨ (¬ p4695) ∨ p3083 ∨ (¬ p4384) ∨ (¬ p2656) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p3355 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4384 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2656 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48186 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u7))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (False.elim (r4 u2)))))))))))))

theorem step74646 (p2437 p2481 p2881 p3083 p3960 p4256 p4277 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h59074 : (¬ p2437) ∨ (¬ p2481) ∨ (¬ p2881) ∨ (¬ p3960) ∨ (¬ p4256) ∨ (¬ p4277))
    : (¬ p2481) ∨ p3083 ∨ (¬ p2881) ∨ (¬ p2437) ∨ (¬ p3960) ∨ (¬ p4277) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2481 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3083) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2437 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3960 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h59074 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u6))) (fun r4 => (False.elim (r4 u5)))))))))))))

theorem step74647 (p2220 p2440 p2542 p3083 p3693 p4256 p4539 : Prop)
    (h73542 : p4256 ∨ p3083)
    (h73270 : p2542 ∨ p2440)
    (h50854 : (¬ p2220) ∨ (¬ p2542) ∨ (¬ p3693) ∨ (¬ p4256) ∨ (¬ p4539))
    : p3083 ∨ (¬ p3693) ∨ p2440 ∨ (¬ p2220) ∨ (¬ p4539) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3083) := (fun h => hn (Or.inl h));
    let u1 : p3693 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2220 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4539 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50854 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74649 (p2440 p2542 p3083 p4149 p4181 p4256 p4286 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73270 : p2542 ∨ p2440)
    (h73542 : p4256 ∨ p3083)
    (h53931 : (¬ p2542) ∨ (¬ p4181) ∨ (¬ p4256) ∨ (¬ p4286))
    : p4149 ∨ (¬ p4181) ∨ p2440 ∨ p3083 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p4181 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53931 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74650 (p3083 p3343 p4149 p4256 p4286 p4695 p5118 : Prop)
    (h73548 : p4286 ∨ p4149)
    (h73542 : p4256 ∨ p3083)
    (h50791 : (¬ p3343) ∨ (¬ p4256) ∨ (¬ p4286) ∨ (¬ p4695) ∨ (¬ p5118))
    : p4149 ∨ (¬ p3343) ∨ p3083 ∨ (¬ p4695) ∨ (¬ p5118) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p4149) := (fun h => hn (Or.inl h));
    let u1 : p3343 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3083) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4695 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5118 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4286 := (Or.elim h73548 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4256 := (Or.elim h73542 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h50791 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74655 (p2437 p2573 p2579 p3389 p3422 p3742 p4753 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73452 : p3742 ∨ p2437)
    (h54223 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3422) ∨ (¬ p3742) ∨ (¬ p4753))
    : p2573 ∨ (¬ p3422) ∨ (¬ p4753) ∨ p2437 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4753 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54223 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74656 (p2573 p2579 p2911 p3389 p3422 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h54222 : (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3422))
    : p2573 ∨ (¬ p3422) ∨ (¬ p3389) ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h54222 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74658 (p2417 p2573 p2579 p3389 p3422 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h46914 : (¬ p2417) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3422))
    : (¬ p2417) ∨ p2573 ∨ (¬ p3422) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3422 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46914 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step74659 (p2230 p2563 p2589 p3201 p3389 p3876 p4110 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73284 : p2589 ∨ p2230)
    (h73516 : p4110 ∨ p2563)
    (h53655 : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4110))
    : p3201 ∨ (¬ p3389) ∨ p2230 ∨ p2563 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2563) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h53655 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u6)))))))))

theorem step74660 (p2230 p2406 p2589 p3201 p3389 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73284 : p2589 ∨ p2230)
    (h47759 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3876))
    : (¬ p3389) ∨ (¬ p2406) ∨ p3201 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47759 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74661 (p2230 p2440 p2542 p2589 p3246 p3389 p3569 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73284 : p2589 ∨ p2230)
    (h47108 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p3246) ∨ (¬ p3389) ∨ (¬ p3569))
    : (¬ p3246) ∨ p2440 ∨ (¬ p3389) ∨ (¬ p3569) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3246 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2440) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47108 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74663 (p2230 p2589 p2901 p3389 p3569 p4320 p4702 : Prop)
    (h73552 : p4320 ∨ p2901)
    (h73284 : p2589 ∨ p2230)
    (h60371 : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4320) ∨ (¬ p4702))
    : p2901 ∨ (¬ p3389) ∨ p2230 ∨ (¬ p4702) ∨ (¬ p3569) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2901) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4320 := (Or.elim h73552 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h60371 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74665 (p2230 p2406 p2589 p2881 p3389 p3569 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h46363 : (¬ p2406) ∨ (¬ p2589) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p3569))
    : (¬ p3389) ∨ (¬ p3569) ∨ p2230 ∨ (¬ p2406) ∨ (¬ p2881) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h46363 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74667 (p2230 p2406 p2417 p2589 p3389 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h46345 : (¬ p2406) ∨ (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389))
    : (¬ p3389) ∨ (¬ p2406) ∨ (¬ p2417) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46345 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74670 (p2177 p2299 p2406 p2911 p3238 p3389 p3519 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h73374 : p3238 ∨ p2406)
    (h47942 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3238) ∨ (¬ p3389) ∨ (¬ p3519))
    : (¬ p3389) ∨ (¬ p3519) ∨ (¬ p2911) ∨ p2177 ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h47942 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74672 (p2437 p2459 p2470 p2476 p3389 p3742 p4348 p4383 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73250 : p2476 ∨ p2470)
    (h73562 : p4348 ∨ p2459)
    (h57037 : (¬ p2476) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4348) ∨ (¬ p4383))
    : (¬ p3389) ∨ p2437 ∨ p2470 ∨ p2459 ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u7 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h57037 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u7))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74673 (p2088 p2474 p2528 p2922 p2928 p3389 p3857 : Prop)
    (h73320 : p2928 ∨ p2922)
    (h73480 : p3857 ∨ p2088)
    (h43623 : (¬ p2474) ∨ (¬ p2528) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p3857))
    : (¬ p3389) ∨ (¬ p2474) ∨ (¬ p2528) ∨ p2922 ∨ p2088 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2474 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2088) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p3857 := (Or.elim h73480 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h43623 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step74674 (p2470 p2476 p2528 p2534 p2922 p2928 p3389 : Prop)
    (h73268 : p2534 ∨ p2528)
    (h73250 : p2476 ∨ p2470)
    (h73320 : p2928 ∨ p2922)
    (h43622 : (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2928) ∨ (¬ p3389))
    : p2528 ∨ (¬ p3389) ∨ p2470 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2528) := (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43622 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74676 (p2417 p2470 p2476 p3389 p4383 p4668 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h60207 : (¬ p2417) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4668))
    : (¬ p2417) ∨ p2470 ∨ (¬ p3389) ∨ (¬ p4668) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60207 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74677 (p2553 p2573 p2579 p2588 p3201 p3389 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73282 : p2588 ∨ p2553)
    (h45701 : (¬ p2579) ∨ (¬ p2588) ∨ (¬ p3389) ∨ (¬ p3876))
    : p3201 ∨ p2573 ∨ (¬ p3389) ∨ p2553 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2553) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45701 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74679 (p2440 p2573 p2579 p3016 p3389 p4646 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h61920 : (¬ p2440) ∨ (¬ p2579) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p4646))
    : (¬ p3016) ∨ p2573 ∨ (¬ p3389) ∨ (¬ p4646) ∨ (¬ p2440) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4646 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h61920 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74680 (p2573 p2579 p3389 p3564 p4137 p4620 p4710 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73524 : p4137 ∨ p3564)
    (h41326 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4620) ∨ (¬ p4710))
    : p2573 ∨ (¬ p4710) ∨ (¬ p4620) ∨ p3564 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4620 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41326 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74681 (p2573 p2579 p3389 p3461 p3564 p4137 p4191 : Prop)
    (h73530 : p4191 ∨ p3461)
    (h73274 : p2579 ∨ p2573)
    (h73524 : p4137 ∨ p3564)
    (h45053 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4137) ∨ (¬ p4191))
    : p3461 ∨ p2573 ∨ p3564 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3461) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3564) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4191 := (Or.elim h73530 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p4137 := (Or.elim h73524 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45053 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74682 (p2406 p2573 p2579 p2922 p2928 p3389 p4715 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73320 : p2928 ∨ p2922)
    (h50412 : (¬ p2406) ∨ (¬ p2579) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4715))
    : (¬ p3389) ∨ (¬ p2406) ∨ (¬ p4715) ∨ p2573 ∨ p2922 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2406 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50412 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u0))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74687 (p2177 p2299 p2573 p2579 p2911 p3389 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73234 : p2299 ∨ p2177)
    (h45481 : (¬ p2299) ∨ (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3389))
    : (¬ p3389) ∨ (¬ p2911) ∨ p2573 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h45481 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74690 (p2573 p2579 p2911 p3016 p3389 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h46915 : (¬ p2579) ∨ (¬ p2911) ∨ (¬ p3016) ∨ (¬ p3389))
    : (¬ p3016) ∨ p2573 ∨ (¬ p2911) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3016 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h46915 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step74692 (p2573 p2579 p3389 p3581 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h20317 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3581))
    : p2573 ∨ (¬ p3581) ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p3581 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h20317 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step74696 (p2417 p2573 p2579 p3389 p3434 p4324 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73556 : p4324 ∨ p3434)
    (h43261 : (¬ p2417) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4324))
    : (¬ p2417) ∨ p2573 ∨ (¬ p3389) ∨ p3434 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3434) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p4324 := (Or.elim h73556 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h43261 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u5)))))))))

theorem step74698 (p2417 p2493 p2573 p2579 p3389 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h45530 : (¬ p2417) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3389))
    : (¬ p2417) ∨ p2573 ∨ (¬ p3389) ∨ (¬ p2493) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h45530 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step74699 (p2437 p2440 p2542 p2573 p2579 p3389 p3742 p4715 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73270 : p2542 ∨ p2440)
    (h73274 : p2579 ∨ p2573)
    (h50355 : (¬ p2542) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4715))
    : (¬ p3389) ∨ p2437 ∨ (¬ p4715) ∨ p2440 ∨ p2573 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2440) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    let u7 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h50355 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74702 (p2177 p2493 p2573 p2579 p3389 p4710 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h45634 : (¬ p2177) ∨ (¬ p2493) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p4710))
    : p2573 ∨ (¬ p4710) ∨ (¬ p2493) ∨ (¬ p3389) ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2493 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h45634 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74709 (p2274 p2573 p2579 p3097 p3389 p4710 p4718 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73352 : p3097 ∨ p2274)
    (h41349 : (¬ p2579) ∨ (¬ p3097) ∨ (¬ p3389) ∨ (¬ p4710) ∨ (¬ p4718))
    : p2573 ∨ (¬ p4710) ∨ (¬ p4718) ∨ p2274 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4718 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2274) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41349 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74710 (p2573 p2579 p2850 p3201 p3389 p3876 p4715 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h50356 : (¬ p2579) ∨ (¬ p2850) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4715))
    : p3201 ∨ p2573 ∨ (¬ p3389) ∨ (¬ p4715) ∨ (¬ p2850) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4715 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50356 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74711 (p2230 p2427 p2589 p2922 p2928 p3389 p4235 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73320 : p2928 ∨ p2922)
    (h73284 : p2589 ∨ p2230)
    (h46664 : (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4235))
    : (¬ p3389) ∨ p2427 ∨ p2922 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46664 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74713 (p2230 p2589 p2881 p2911 p3389 p3570 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h73284 : p2589 ∨ p2230)
    (h56521 : (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3570))
    : (¬ p2911) ∨ (¬ p3389) ∨ p2881 ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h56521 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74714 (p2230 p2417 p2449 p2589 p3389 p3947 : Prop)
    (h73494 : p3947 ∨ p2449)
    (h73284 : p2589 ∨ p2230)
    (h54483 : (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3947))
    : (¬ p2417) ∨ p2449 ∨ (¬ p3389) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2449) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3947 := (Or.elim h73494 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h54483 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74717 (p2352 p2573 p2579 p3389 p3956 p4710 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73500 : p3956 ∨ p2352)
    (h71242 : (¬ p3956) ∨ (¬ p3389) ∨ (¬ p2579) ∨ (¬ p4710))
    : p2573 ∨ (¬ p4710) ∨ p2352 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2352) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p3956 := (Or.elim h73500 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h71242 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74718 (p2230 p2589 p2911 p3389 p3527 p3548 : Prop)
    (h73404 : p3548 ∨ p3527)
    (h73284 : p2589 ∨ p2230)
    (h42861 : (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3548))
    : p3527 ∨ (¬ p2911) ∨ p2230 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3527) := (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3548 := (Or.elim h73404 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42861 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74719 (p2341 p2911 p3362 p3389 p3551 p5260 : Prop)
    (h73408 : p3551 ∨ p2341)
    (h41203 : (¬ p2911) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3551) ∨ (¬ p5260))
    : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3362) ∨ p2341 ∨ (¬ p5260) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2341) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p5260 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3551 := (Or.elim h73408 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41203 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74720 (p2177 p2299 p2911 p3346 p3389 : Prop)
    (h73234 : p2299 ∨ p2177)
    (h44513 : (¬ p2299) ∨ (¬ p2911) ∨ (¬ p3346) ∨ (¬ p3389))
    : (¬ p3346) ∨ (¬ p3389) ∨ p2177 ∨ (¬ p2911) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44513 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74722 (p2177 p2470 p2476 p3389 p4276 p4383 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h41686 : (¬ p2177) ∨ (¬ p2476) ∨ (¬ p3389) ∨ (¬ p4276) ∨ (¬ p4383))
    : (¬ p3389) ∨ (¬ p4383) ∨ (¬ p4276) ∨ p2470 ∨ (¬ p2177) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4276 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2470) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2177 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41686 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74725 (p2295 p2573 p2579 p3389 p3568 p4710 p4973 : Prop)
    (h73274 : p2579 ∨ p2573)
    (h73416 : p3568 ∨ p2295)
    (h41145 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3568) ∨ (¬ p4710) ∨ (¬ p4973))
    : p2573 ∨ (¬ p4710) ∨ (¬ p4973) ∨ p2295 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2573) := (fun h => hn (Or.inl h));
    let u1 : p4710 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4973 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2295) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41145 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74728 (p2470 p2476 p2881 p3389 p4277 p4383 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h50250 : (¬ p2476) ∨ (¬ p2881) ∨ (¬ p3389) ∨ (¬ p4277) ∨ (¬ p4383))
    : (¬ p3389) ∨ p2470 ∨ (¬ p2881) ∨ (¬ p4277) ∨ (¬ p4383) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2881 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4277 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4383 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h50250 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74730 (p2230 p2589 p2850 p2911 p3389 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h49138 : (¬ p2589) ∨ (¬ p2850) ∨ (¬ p2911) ∨ (¬ p3389))
    : (¬ p3389) ∨ (¬ p2850) ∨ (¬ p2911) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2850 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49138 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74731 (p2230 p2437 p2589 p3016 p3389 p3742 p4717 : Prop)
    (h73452 : p3742 ∨ p2437)
    (h73284 : p2589 ∨ p2230)
    (h41362 : (¬ p2589) ∨ (¬ p3016) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4717))
    : (¬ p3389) ∨ p2437 ∨ (¬ p4717) ∨ (¬ p3016) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2437) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3016 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h41362 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74732 (p2230 p2440 p2542 p2589 p2922 p2928 p3389 p4811 : Prop)
    (h73270 : p2542 ∨ p2440)
    (h73320 : p2928 ∨ p2922)
    (h73284 : p2589 ∨ p2230)
    (h56700 : (¬ p2542) ∨ (¬ p2589) ∨ (¬ p2928) ∨ (¬ p3389) ∨ (¬ p4811))
    : p2440 ∨ p2922 ∨ (¬ p3389) ∨ (¬ p4811) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2440) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2922) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4811 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2542 := (Or.elim h73270 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u7 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h56700 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u7))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74736 (p2230 p2441 p2589 p3389 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h20343 : (¬ p2441) ∨ (¬ p2589) ∨ (¬ p3389))
    : (¬ p3389) ∨ (¬ p2441) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2441 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h20343 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u0)))))))

theorem step74743 (p2230 p2396 p2417 p2589 p3389 p4107 : Prop)
    (h73514 : p4107 ∨ p2396)
    (h73284 : p2589 ∨ p2230)
    (h54959 : (¬ p2417) ∨ (¬ p2589) ∨ (¬ p3389) ∨ (¬ p4107))
    : (¬ p2417) ∨ p2396 ∨ p2230 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2417 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2396) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4107 := (Or.elim h73514 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h54959 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74756 (p2501 p2573 p2579 p3309 p3389 p3549 p4710 : Prop)
    (h73406 : p3549 ∨ p3309)
    (h73274 : p2579 ∨ p2573)
    (h41146 : (¬ p2501) ∨ (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3549) ∨ (¬ p4710))
    : (¬ p4710) ∨ p3309 ∨ (¬ p3389) ∨ p2573 ∨ (¬ p2501) :=
  Classical.byContradiction (fun hn =>
    let u0 : p4710 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3309) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2573) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2501 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3549 := (Or.elim h73406 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41146 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u0)))))))))))

theorem step74757 (p2417 p2696 p2761 p2797 p3365 p3366 p3389 p3519 p4195 p4376 p5254 p5717 : Prop)
    (h73532 : p4195 ∨ p2797)
    (h73390 : p3365 ∨ p2696)
    (h65021 : (¬ p2417) ∨ (¬ p2761) ∨ (¬ p3365) ∨ (¬ p3366) ∨ (¬ p3389) ∨ (¬ p3519) ∨ (¬ p4195) ∨ (¬ p4376) ∨ (¬ p5254) ∨ (¬ p5717))
    : (¬ p5717) ∨ p2797 ∨ (¬ p5254) ∨ p2696 ∨ (¬ p3389) ∨ (¬ p3366) ∨ (¬ p2417) ∨ (¬ p3519) ∨ (¬ p4376) ∨ (¬ p2761) :=
  Classical.byContradiction (fun hn =>
    let u0 : p5717 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2797) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p5254 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2696) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p3366 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p2417 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : p4376 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))));
    let u9 : p2761 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))))));
    let u10 : p4195 := (Or.elim h73532 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u11 : p3365 := (Or.elim h73390 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h65021 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u9))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u11))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u4))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u8))) (fun r7 => (Or.elim r7 (fun q8 => (False.elim (q8 u2))) (fun r8 => (False.elim (r8 u0)))))))))))))))))))))

theorem step74758 (p2177 p2230 p2299 p2589 p2911 p3389 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h73234 : p2299 ∨ p2177)
    (h62595 : (¬ p2299) ∨ (¬ p2589) ∨ (¬ p2911) ∨ (¬ p3389))
    : (¬ p3389) ∨ (¬ p2911) ∨ p2230 ∨ p2177 :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2911 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2177) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u5 : p2299 := (Or.elim h73234 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h62595 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u0)))))))))

theorem step74762 (p2922 p2928 p3276 p3346 p3389 p4425 : Prop)
    (h73578 : p4425 ∨ p3276)
    (h73320 : p2928 ∨ p2922)
    (h52379 : (¬ p2928) ∨ (¬ p3346) ∨ (¬ p3389) ∨ (¬ p4425))
    : (¬ p3346) ∨ p3276 ∨ p2922 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3276) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2922) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4425 := (Or.elim h73578 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2928 := (Or.elim h73320 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52379 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74765 (p2437 p2761 p3346 p3389 p3742 p4381 p4636 : Prop)
    (h73574 : p4381 ∨ p2761)
    (h73452 : p3742 ∨ p2437)
    (h59119 : (¬ p3346) ∨ (¬ p3389) ∨ (¬ p3742) ∨ (¬ p4381) ∨ (¬ p4636))
    : (¬ p3346) ∨ p2761 ∨ (¬ p4636) ∨ p2437 ∨ (¬ p3389) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3346 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2761) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4636 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2437) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4381 := (Or.elim h73574 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3742 := (Or.elim h73452 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h59119 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74767 (p2573 p2579 p3201 p3367 p3389 p3585 p3876 : Prop)
    (h73486 : p3876 ∨ p3201)
    (h73274 : p2579 ∨ p2573)
    (h73428 : p3585 ∨ p3367)
    (h50215 : (¬ p2579) ∨ (¬ p3389) ∨ (¬ p3585) ∨ (¬ p3876))
    : p3201 ∨ p2573 ∨ (¬ p3389) ∨ p3367 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3201) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2573) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3367) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2579 := (Or.elim h73274 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p3585 := (Or.elim h73428 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h50215 (fun q0 => (False.elim (q0 u5))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74768 (p2352 p2383 p2387 p2577 p3389 p4711 : Prop)
    (h73246 : p2387 ∨ p2383)
    (h41425 : (¬ p2352) ∨ (¬ p2387) ∨ (¬ p2577) ∨ (¬ p3389) ∨ (¬ p4711))
    : (¬ p2577) ∨ (¬ p4711) ∨ (¬ p3389) ∨ p2383 ∨ (¬ p2352) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2577 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h41425 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u1)))))))))))

theorem step74770 (p2577 p3389 p3564 p3654 p3946 p4711 : Prop)
    (h73492 : p3946 ∨ p3654)
    (h60747 : (¬ p2577) ∨ (¬ p3389) ∨ (¬ p3564) ∨ (¬ p3946) ∨ (¬ p4711))
    : (¬ p3564) ∨ p3654 ∨ (¬ p3389) ∨ (¬ p2577) ∨ (¬ p4711) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3654) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2577 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4711 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3946 := (Or.elim h73492 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h60747 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74773 (p2230 p2563 p2589 p3389 p3569 p4110 p4558 : Prop)
    (h73516 : p4110 ∨ p2563)
    (h73284 : p2589 ∨ p2230)
    (h49683 : (¬ p2589) ∨ (¬ p3389) ∨ (¬ p3569) ∨ (¬ p4110) ∨ (¬ p4558))
    : (¬ p3389) ∨ p2563 ∨ (¬ p3569) ∨ p2230 ∨ (¬ p4558) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3389 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2563) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3569 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4558 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4110 := (Or.elim h73516 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h49683 (fun q0 => (False.elim (q0 u6))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74778 (p2881 p2911 p3367 p3389 p3570 p3759 : Prop)
    (h73418 : p3570 ∨ p2881)
    (h46124 : (¬ p2911) ∨ (¬ p3367) ∨ (¬ p3389) ∨ (¬ p3570) ∨ (¬ p3759))
    : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3367) ∨ p2881 ∨ (¬ p3759) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3367 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2881) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3570 := (Or.elim h73418 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46124 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74780 (p2383 p2387 p2668 p2787 p3201 p3323 p3333 p3362 p3389 p3876 p4037 p5322 : Prop)
    (h73508 : p4037 ∨ p3323)
    (h73486 : p3876 ∨ p3201)
    (h73246 : p2387 ∨ p2383)
    (h55354 : (¬ p2387) ∨ (¬ p2668) ∨ (¬ p2787) ∨ (¬ p3333) ∨ (¬ p3362) ∨ (¬ p3389) ∨ (¬ p3876) ∨ (¬ p4037) ∨ (¬ p5322))
    : p3323 ∨ (¬ p3333) ∨ (¬ p2787) ∨ (¬ p3362) ∨ p3201 ∨ (¬ p2668) ∨ (¬ p5322) ∨ (¬ p3389) ∨ p2383 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3323) := (fun h => hn (Or.inl h));
    let u1 : p3333 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2787 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3362 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p3201) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2668 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))));
    let u6 : p5322 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))));
    let u7 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))));
    let u8 : (¬ p2383) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))));
    let u9 : p4037 := (Or.elim h73508 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u10 : p3876 := (Or.elim h73486 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    let u11 : p2387 := (Or.elim h73246 (fun q0 => q0) (fun r0 => (False.elim (u8 r0))));
    (Or.elim h55354 (fun q0 => (False.elim (q0 u11))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u3))) (fun r4 => (Or.elim r4 (fun q5 => (False.elim (q5 u7))) (fun r5 => (Or.elim r5 (fun q6 => (False.elim (q6 u10))) (fun r6 => (Or.elim r6 (fun q7 => (False.elim (q7 u9))) (fun r7 => (False.elim (r7 u6)))))))))))))))))))

theorem step74786 (p2470 p2476 p2510 p2573 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h19229 : (¬ p2476) ∨ (¬ p2510) ∨ (¬ p2573))
    : (¬ p2510) ∨ p2470 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2510 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2470) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h19229 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (False.elim (r1 u2)))))))

theorem step74788 (p2470 p2476 p2553 p2573 p4432 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h71243 : (¬ p4432) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p2553))
    : p2470 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p4432) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h71243 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u1)))))))))

theorem step74791 (p2363 p2470 p2476 p2528 p2534 p2573 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h47449 : (¬ p2363) ∨ (¬ p2476) ∨ (¬ p2534) ∨ (¬ p2573))
    : p2470 ∨ p2528 ∨ (¬ p2573) ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    (Or.elim h47449 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u2)))))))))

theorem step74794 (p2470 p2476 p2493 p2499 p2528 p2534 p2573 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h73268 : p2534 ∨ p2528)
    (h73260 : p2499 ∨ p2493)
    (h42929 : (¬ p2476) ∨ (¬ p2499) ∨ (¬ p2534) ∨ (¬ p2573))
    : p2470 ∨ p2528 ∨ p2493 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : (¬ p2528) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2493) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2534 := (Or.elim h73268 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2499 := (Or.elim h73260 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42929 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u3)))))))))

theorem step74796 (p2230 p2363 p2510 p2528 p2573 p2589 p4347 : Prop)
    (h73560 : p4347 ∨ p2363)
    (h73284 : p2589 ∨ p2230)
    (h52682 : (¬ p2510) ∨ (¬ p2528) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p4347))
    : p2363 ∨ (¬ p2510) ∨ p2230 ∨ (¬ p2573) ∨ (¬ p2528) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2363) := (fun h => hn (Or.inl h));
    let u1 : p2510 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2528 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4347 := (Or.elim h73560 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h52682 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u6))) (fun r3 => (False.elim (r3 u5)))))))))))

theorem step74801 (p2187 p2352 p2406 p2573 p3238 p3519 p3989 : Prop)
    (h73374 : p3238 ∨ p2406)
    (h73502 : p3989 ∨ p2187)
    (h47431 : (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3238) ∨ (¬ p3519) ∨ (¬ p3989))
    : (¬ p2573) ∨ (¬ p2352) ∨ p2406 ∨ p2187 ∨ (¬ p3519) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3519 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    let u6 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h47431 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u4))) (fun r3 => (False.elim (r3 u6)))))))))))

theorem step74802 (p2352 p2363 p2459 p2573 p4348 : Prop)
    (h73562 : p4348 ∨ p2459)
    (h62560 : (¬ p2352) ∨ (¬ p2363) ∨ (¬ p2573) ∨ (¬ p4348))
    : (¬ p2352) ∨ (¬ p2573) ∨ p2459 ∨ (¬ p2363) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2459) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2363 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p4348 := (Or.elim h73562 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62560 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74806 (p2230 p2573 p2589 p3125 p3564 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h73284 : p2589 ∨ p2230)
    (h45710 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3564) ∨ (¬ p3744))
    : (¬ p3564) ∨ p3125 ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3125) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h45710 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74807 (p2274 p2573 p3125 p3564 p3744 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h42771 : (¬ p2274) ∨ (¬ p2573) ∨ (¬ p3564) ∨ (¬ p3744))
    : (¬ p3564) ∨ (¬ p2274) ∨ p3125 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3564 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h42771 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u0))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74808 (p2230 p2573 p2589 p2590 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h3306 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p2590))
    : (¬ p2573) ∨ (¬ p2590) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2590 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h3306 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (False.elim (r1 u1)))))))

theorem step74819 (p2406 p2573 p2922 p3238 p3389 p3540 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h73374 : p3238 ∨ p2406)
    (h44842 : (¬ p2573) ∨ (¬ p2922) ∨ (¬ p3238) ∨ (¬ p3540))
    : (¬ p2922) ∨ p3389 ∨ (¬ p2573) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2922 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p3389) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h44842 (fun q0 => (False.elim (q0 u2))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74820 (p2406 p2573 p3193 p3222 p3238 p3346 p4717 : Prop)
    (h73364 : p3222 ∨ p3193)
    (h73374 : p3238 ∨ p2406)
    (h53669 : (¬ p2573) ∨ (¬ p3222) ∨ (¬ p3238) ∨ (¬ p3346) ∨ (¬ p4717))
    : p3193 ∨ (¬ p3346) ∨ (¬ p4717) ∨ (¬ p2573) ∨ p2406 :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3193) := (fun h => hn (Or.inl h));
    let u1 : p3346 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4717 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2406) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3222 := (Or.elim h73364 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p3238 := (Or.elim h73374 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h53669 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u6))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u1))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74822 (p2230 p2274 p2553 p2573 p2589 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h73284 : p2589 ∨ p2230)
    (h44843 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3097))
    : (¬ p2553) ∨ p2274 ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2553 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2274) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h44843 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74823 (p2573 p3125 p3367 p3564 p3744 p3759 : Prop)
    (h73454 : p3744 ∨ p3125)
    (h46251 : (¬ p2573) ∨ (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3744) ∨ (¬ p3759))
    : (¬ p3367) ∨ (¬ p3564) ∨ (¬ p3759) ∨ p3125 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p3367 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3564 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3759 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p3125) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3744 := (Or.elim h73454 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h46251 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

theorem step74827 (p2230 p2284 p2573 p2589 p3952 p4203 p4702 : Prop)
    (h73496 : p3952 ∨ p2284)
    (h73284 : p2589 ∨ p2230)
    (h41709 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3952) ∨ (¬ p4203) ∨ (¬ p4702))
    : p2284 ∨ (¬ p2573) ∨ p2230 ∨ (¬ p4203) ∨ (¬ p4702) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2284) := (fun h => hn (Or.inl h));
    let u1 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p4702 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3952 := (Or.elim h73496 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h41709 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u3))) (fun r3 => (False.elim (r3 u4)))))))))))

theorem step74828 (p2274 p2573 p3389 p3540 p3921 p3958 : Prop)
    (h73402 : p3540 ∨ p3389)
    (h51811 : (¬ p2274) ∨ (¬ p2573) ∨ (¬ p3540) ∨ (¬ p3921) ∨ (¬ p3958))
    : p3389 ∨ (¬ p2274) ∨ (¬ p3921) ∨ (¬ p3958) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p3389) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3921 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3540 := (Or.elim h73402 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h51811 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u4))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74831 (p2230 p2352 p2406 p2573 p2589 : Prop)
    (h73284 : p2589 ∨ p2230)
    (h62459 : (¬ p2352) ∨ (¬ p2406) ∨ (¬ p2573) ∨ (¬ p2589))
    : (¬ p2406) ∨ (¬ p2352) ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2406 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2352 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h62459 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74832 (p2187 p2274 p2553 p2573 p3097 : Prop)
    (h73352 : p3097 ∨ p2274)
    (h47846 : (¬ p2187) ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p3097))
    : p2274 ∨ (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2187) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2274) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3097 := (Or.elim h73352 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h47846 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u1))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74839 (p2230 p2295 p2553 p2573 p2589 p3568 : Prop)
    (h73416 : p3568 ∨ p2295)
    (h73284 : p2589 ∨ p2230)
    (h43336 : (¬ p2553) ∨ (¬ p2573) ∨ (¬ p2589) ∨ (¬ p3568))
    : p2295 ∨ (¬ p2553) ∨ p2230 ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2295) := (fun h => hn (Or.inl h));
    let u1 : p2553 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3568 := (Or.elim h73416 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u5 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u2 r0))));
    (Or.elim h43336 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u3))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u5))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74840 (p2230 p2427 p2573 p2589 p4203 p4235 p4555 : Prop)
    (h73536 : p4235 ∨ p2427)
    (h73284 : p2589 ∨ p2230)
    (h62454 : (¬ p2573) ∨ (¬ p2589) ∨ (¬ p4203) ∨ (¬ p4235) ∨ (¬ p4555))
    : (¬ p2573) ∨ p2427 ∨ (¬ p4203) ∨ (¬ p4555) ∨ p2230 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2573 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : (¬ p2427) := (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4203 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4555 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : (¬ p2230) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p4235 := (Or.elim h73536 (fun q0 => q0) (fun r0 => (False.elim (u1 r0))));
    let u6 : p2589 := (Or.elim h73284 (fun q0 => q0) (fun r0 => (False.elim (u4 r0))));
    (Or.elim h62454 (fun q0 => (False.elim (q0 u0))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74841 (p2187 p2274 p2352 p2573 p3989 : Prop)
    (h73502 : p3989 ∨ p2187)
    (h42645 : (¬ p2274) ∨ (¬ p2352) ∨ (¬ p2573) ∨ (¬ p3989))
    : (¬ p2352) ∨ (¬ p2274) ∨ (¬ p2573) ∨ p2187 :=
  Classical.byContradiction (fun hn =>
    let u0 : p2352 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2187) := (fun h => hn (Or.inr (Or.inr (Or.inr h))));
    let u4 : p3989 := (Or.elim h73502 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h42645 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u2))) (fun r2 => (False.elim (r2 u4)))))))))

theorem step74842 (p2187 p2470 p2476 p2573 p3958 p4432 : Prop)
    (h73250 : p2476 ∨ p2470)
    (h55497 : (¬ p2187) ∨ (¬ p2476) ∨ (¬ p2573) ∨ (¬ p3958) ∨ (¬ p4432))
    : p2470 ∨ (¬ p2187) ∨ (¬ p3958) ∨ (¬ p4432) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2470) := (fun h => hn (Or.inl h));
    let u1 : p2187 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p3958 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p4432 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p2476 := (Or.elim h73250 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h55497 (fun q0 => (False.elim (q0 u1))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u5))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u4))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (False.elim (r3 u3)))))))))))

theorem step74846 (p2274 p2440 p2553 p2573 p2588 p2665 p3051 p4557 : Prop)
    (h73282 : p2588 ∨ p2553)
    (h73636 : p4557 ∨ (¬ p2274))
    (h66960 : (¬ p4557) ∨ (¬ p2588) ∨ (¬ p2665) ∨ (¬ p2440) ∨ (¬ p2573) ∨ (¬ p3051))
    : p2553 ∨ (¬ p2274) ∨ (¬ p2440) ∨ (¬ p2665) ∨ (¬ p3051) ∨ (¬ p2573) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2553) := (fun h => hn (Or.inl h));
    let u1 : p2274 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2440 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p3051 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))));
    let u5 : p2573 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))));
    let u6 : p2588 := (Or.elim h73282 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    let u7 : p4557 := (Or.elim h73636 (fun q0 => q0) (fun r0 => (False.elim (r0 u1))));
    (Or.elim h66960 (fun q0 => (False.elim (q0 u7))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u6))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u3))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u2))) (fun r3 => (Or.elim r3 (fun q4 => (False.elim (q4 u5))) (fun r4 => (False.elim (r4 u4)))))))))))))

theorem step74850 (p2651 p2657 p2807 p4112 : Prop)
    (h73288 : p2657 ∨ p2651)
    (h19868 : (¬ p2657) ∨ (¬ p2807) ∨ (¬ p4112))
    : p2651 ∨ (¬ p4112) ∨ (¬ p2807) :=
  Classical.byContradiction (fun hn =>
    let u0 : (¬ p2651) := (fun h => hn (Or.inl h));
    let u1 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p2807 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr h)));
    let u3 : p2657 := (Or.elim h73288 (fun q0 => q0) (fun r0 => (False.elim (u0 r0))));
    (Or.elim h19868 (fun q0 => (False.elim (q0 u3))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u2))) (fun r1 => (False.elim (r1 u1)))))))

theorem step74852 (p2264 p2665 p2911 p3389 p3553 p4112 : Prop)
    (h73410 : p3553 ∨ p2264)
    (h48943 : (¬ p2665) ∨ (¬ p2911) ∨ (¬ p3389) ∨ (¬ p3553) ∨ (¬ p4112))
    : (¬ p2911) ∨ (¬ p3389) ∨ (¬ p4112) ∨ p2264 ∨ (¬ p2665) :=
  Classical.byContradiction (fun hn =>
    let u0 : p2911 := Classical.byContradiction (fun h => hn (Or.inl h));
    let u1 : p3389 := Classical.byContradiction (fun h => hn (Or.inr (Or.inl h)));
    let u2 : p4112 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inl h))));
    let u3 : (¬ p2264) := (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h)))));
    let u4 : p2665 := Classical.byContradiction (fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h)))));
    let u5 : p3553 := (Or.elim h73410 (fun q0 => q0) (fun r0 => (False.elim (u3 r0))));
    (Or.elim h48943 (fun q0 => (False.elim (q0 u4))) (fun r0 => (Or.elim r0 (fun q1 => (False.elim (q1 u0))) (fun r1 => (Or.elim r1 (fun q2 => (False.elim (q2 u1))) (fun r2 => (Or.elim r2 (fun q3 => (False.elim (q3 u5))) (fun r3 => (False.elim (r3 u2)))))))))))

end ElevenRUP
