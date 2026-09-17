import Erdos261Finite.Cert015

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace Erdos261Finite

theorem cert_371593 : Represents 3787 3785 :=
  segment 157 3787 3785 3944 1080 (by rfl) cert_359527

theorem cert_371712 : Represents 3874 1726 :=
  segment 118 3874 1726 3992 0 (by rfl) (zero_represents 3992)

theorem cert_371730 : Represents 3856 3850 :=
  segment 18 3856 3850 3874 1726 (by rfl) cert_371712

theorem cert_371798 : Represents 3788 3786 :=
  segment 68 3788 3786 3856 3850 (by rfl) cert_371730

theorem cert_371809 : Represents 4390 1896 :=
  segment 10 4390 1896 4400 4296 (by rfl) cert_175087

theorem cert_371903 : Represents 4296 856 :=
  segment 94 4296 856 4390 1896 (by rfl) cert_371809

theorem cert_371965 : Represents 4234 4054 :=
  segment 62 4234 4054 4296 856 (by rfl) cert_371903

theorem cert_372039 : Represents 4160 2304 :=
  segment 74 4160 2304 4234 4054 (by rfl) cert_371965

theorem cert_372097 : Represents 4102 2120 :=
  segment 58 4102 2120 4160 2304 (by rfl) cert_372039

theorem cert_372147 : Represents 4052 4050 :=
  segment 50 4052 4050 4102 2120 (by rfl) cert_372097

theorem cert_372403 : Represents 3796 3286 :=
  segment 256 3796 3286 4052 4050 (by rfl) cert_372147

theorem cert_372410 : Represents 3789 3787 :=
  segment 7 3789 3787 3796 3286 (by rfl) cert_372403

theorem cert_372565 : Represents 3790 3788 :=
  segment 154 3790 3788 3944 2866 (by rfl) cert_337730

theorem cert_372568 : Represents 3838 3824 :=
  segment 2 3838 3824 3840 3778 (by rfl) cert_329860

theorem cert_372615 : Represents 3791 3789 :=
  segment 47 3791 3789 3838 3824 (by rfl) cert_372568

theorem cert_372690 : Represents 3894 3192 :=
  segment 74 3894 3192 3968 1504 (by rfl) cert_219016

theorem cert_372712 : Represents 3872 1920 :=
  segment 22 3872 1920 3894 3192 (by rfl) cert_372690

theorem cert_372792 : Represents 3792 3790 :=
  segment 80 3792 3790 3872 1920 (by rfl) cert_372712

theorem cert_372808 : Represents 3793 3791 :=
  segment 15 3793 3791 3808 2048 (by rfl) cert_343923

theorem cert_372823 : Represents 3794 3792 :=
  segment 14 3794 3792 3808 2946 (by rfl) cert_319895

theorem cert_372839 : Represents 3795 3793 :=
  segment 15 3795 3793 3810 2118 (by rfl) cert_316444

theorem cert_372842 : Represents 3796 3794 :=
  segment 2 3796 3794 3798 3784 (by rfl) cert_329902

theorem cert_372884 : Represents 3797 3795 :=
  segment 41 3797 3795 3838 2552 (by rfl) cert_366197

theorem cert_372925 : Represents 4058 3982 :=
  segment 40 4058 3982 4098 3078 (by rfl) cert_306060

theorem cert_373013 : Represents 3970 510 :=
  segment 88 3970 510 4058 3982 (by rfl) cert_372925

theorem cert_373185 : Represents 3798 3796 :=
  segment 172 3798 3796 3970 510 (by rfl) cert_373013

theorem cert_373193 : Represents 3799 3797 :=
  segment 7 3799 3797 3806 3296 (by rfl) cert_360821

theorem cert_373282 : Represents 3800 3798 :=
  segment 88 3800 3798 3888 360 (by rfl) cert_361051

theorem cert_373322 : Represents 3801 3799 :=
  segment 39 3801 3799 3840 1856 (by rfl) cert_368611

theorem cert_373419 : Represents 4006 1320 :=
  segment 96 4006 1320 4102 88 (by rfl) cert_228248

theorem cert_373425 : Represents 4000 3522 :=
  segment 6 4000 3522 4006 1320 (by rfl) cert_373419

theorem cert_373555 : Represents 3870 1032 :=
  segment 130 3870 1032 4000 3522 (by rfl) cert_373425

theorem cert_373623 : Represents 3802 3800 :=
  segment 68 3802 3800 3870 1032 (by rfl) cert_373555

theorem cert_373654 : Represents 6872 1682 :=
  segment 30 6872 1682 6902 1816 (by rfl) cert_6473

theorem cert_373806 : Represents 6720 4354 :=
  segment 152 6720 4354 6872 1682 (by rfl) cert_373654

theorem cert_373862 : Represents 6664 2930 :=
  segment 56 6664 2930 6720 4354 (by rfl) cert_373806

theorem cert_373894 : Represents 6632 1464 :=
  segment 32 6632 1464 6664 2930 (by rfl) cert_373862

theorem cert_374028 : Represents 6498 2086 :=
  segment 134 6498 2086 6632 1464 (by rfl) cert_373894

theorem cert_374094 : Represents 6432 3266 :=
  segment 66 6432 3266 6498 2086 (by rfl) cert_374028

theorem cert_374198 : Represents 6328 3680 :=
  segment 104 6328 3680 6432 3266 (by rfl) cert_374094

theorem cert_374318 : Represents 6208 2144 :=
  segment 120 6208 2144 6328 3680 (by rfl) cert_374198

theorem cert_374348 : Represents 6178 582 :=
  segment 30 6178 582 6208 2144 (by rfl) cert_374318

theorem cert_374382 : Represents 6144 1152 :=
  segment 34 6144 1152 6178 582 (by rfl) cert_374348

theorem cert_374638 : Represents 5888 4224 :=
  segment 256 5888 4224 6144 1152 (by rfl) cert_374382

theorem cert_374668 : Represents 5858 5856 :=
  segment 30 5858 5856 5888 4224 (by rfl) cert_374638

theorem cert_374680 : Represents 5846 784 :=
  segment 12 5846 784 5858 5856 (by rfl) cert_374668

theorem cert_374696 : Represents 5830 344 :=
  segment 16 5830 344 5846 784 (by rfl) cert_374680

theorem cert_374734 : Represents 5792 458 :=
  segment 38 5792 458 5830 344 (by rfl) cert_374696

theorem cert_374742 : Represents 5784 3776 :=
  segment 8 5784 3776 5792 458 (by rfl) cert_374734

theorem cert_374766 : Represents 5760 1786 :=
  segment 24 5760 1786 5784 3776 (by rfl) cert_374742

theorem cert_375022 : Represents 5504 4952 :=
  segment 256 5504 4952 5760 1786 (by rfl) cert_374766

theorem cert_375198 : Represents 5328 5160 :=
  segment 176 5328 5160 5504 4952 (by rfl) cert_375022

theorem cert_375246 : Represents 5280 3488 :=
  segment 48 5280 3488 5328 5160 (by rfl) cert_375198

theorem cert_375308 : Represents 5218 3102 :=
  segment 62 5218 3102 5280 3488 (by rfl) cert_375246

theorem cert_375348 : Represents 5178 2190 :=
  segment 40 5178 2190 5218 3102 (by rfl) cert_375308

theorem cert_375470 : Represents 5056 4162 :=
  segment 122 5056 4162 5178 2190 (by rfl) cert_375348

theorem cert_375476 : Represents 5050 1486 :=
  segment 6 5050 1486 5056 4162 (by rfl) cert_375470

theorem cert_375494 : Represents 5032 4448 :=
  segment 18 5032 4448 5050 1486 (by rfl) cert_375476

theorem cert_375542 : Represents 4984 4096 :=
  segment 48 4984 4096 5032 4448 (by rfl) cert_375494

theorem cert_375566 : Represents 4960 2368 :=
  segment 24 4960 2368 4984 4096 (by rfl) cert_375542

theorem cert_375582 : Represents 4944 3480 :=
  segment 16 4944 3480 4960 2368 (by rfl) cert_375566

theorem cert_375606 : Represents 4920 2202 :=
  segment 24 4920 2202 4944 3480 (by rfl) cert_375582

theorem cert_375638 : Represents 4888 3752 :=
  segment 32 4888 3752 4920 2202 (by rfl) cert_375606

theorem cert_375692 : Represents 4834 3742 :=
  segment 54 4834 3742 4888 3752 (by rfl) cert_375638

theorem cert_375704 : Represents 4822 272 :=
  segment 12 4822 272 4834 3742 (by rfl) cert_375692

theorem cert_375846 : Represents 4680 2762 :=
  segment 142 4680 2762 4822 272 (by rfl) cert_375704

theorem cert_375848 : Represents 4678 4200 :=
  segment 2 4678 4200 4680 2762 (by rfl) cert_375846

theorem cert_375888 : Represents 4638 4504 :=
  segment 40 4638 4504 4678 4200 (by rfl) cert_375848

theorem cert_376012 : Represents 4514 3686 :=
  segment 124 4514 3686 4638 4504 (by rfl) cert_375888

theorem cert_376022 : Represents 4504 1544 :=
  segment 10 4504 1544 4514 3686 (by rfl) cert_376012

theorem cert_376046 : Represents 4480 3426 :=
  segment 24 4480 3426 4504 1544 (by rfl) cert_376022

theorem cert_376086 : Represents 4440 4402 :=
  segment 40 4440 4402 4480 3426 (by rfl) cert_376046

theorem cert_376110 : Represents 4416 3608 :=
  segment 24 4416 3608 4440 4402 (by rfl) cert_376086

theorem cert_376240 : Represents 4286 2824 :=
  segment 130 4286 2824 4416 3608 (by rfl) cert_376110

theorem cert_376296 : Represents 4230 4176 :=
  segment 56 4230 4176 4286 2824 (by rfl) cert_376240

theorem cert_376318 : Represents 4208 1928 :=
  segment 22 4208 1928 4230 4176 (by rfl) cert_376296

theorem cert_376406 : Represents 4120 1274 :=
  segment 88 4120 1274 4208 1928 (by rfl) cert_376318

theorem cert_376524 : Represents 4002 4000 :=
  segment 118 4002 4000 4120 1274 (by rfl) cert_376406

theorem cert_376723 : Represents 3803 3801 :=
  segment 199 3803 3801 4002 4000 (by rfl) cert_376524

theorem cert_376768 : Represents 3842 1918 :=
  segment 44 3842 1918 3886 1544 (by rfl) cert_357024

theorem cert_376806 : Represents 3804 3802 :=
  segment 38 3804 3802 3842 1918 (by rfl) cert_376768

theorem cert_376879 : Represents 4296 402 :=
  segment 72 4296 402 4368 3706 (by rfl) cert_338926

theorem cert_376927 : Represents 4248 1832 :=
  segment 48 4248 1832 4296 402 (by rfl) cert_376879

theorem cert_376937 : Represents 4238 3728 :=
  segment 10 4238 3728 4248 1832 (by rfl) cert_376927

theorem cert_377079 : Represents 4096 2648 :=
  segment 142 4096 2648 4238 3728 (by rfl) cert_376937

theorem cert_377095 : Represents 4080 2712 :=
  segment 16 4080 2712 4096 2648 (by rfl) cert_377079

theorem cert_377109 : Represents 4066 3358 :=
  segment 14 4066 3358 4080 2712 (by rfl) cert_377095

theorem cert_377269 : Represents 3906 3422 :=
  segment 160 3906 3422 4066 3358 (by rfl) cert_377109

theorem cert_377301 : Represents 3874 862 :=
  segment 32 3874 862 3906 3422 (by rfl) cert_377269

theorem cert_377335 : Represents 3840 2810 :=
  segment 34 3840 2810 3874 862 (by rfl) cert_377301

theorem cert_377370 : Represents 3805 3803 :=
  segment 35 3805 3803 3840 2810 (by rfl) cert_377335

theorem cert_377407 : Represents 3806 3804 :=
  segment 36 3806 3804 3842 262 (by rfl) cert_346245

theorem cert_377409 : Represents 3807 3805 :=
  segment 1 3807 3805 3808 3802 (by rfl) cert_361528

theorem cert_377444 : Represents 3808 3806 :=
  segment 34 3808 3806 3842 2942 (by rfl) cert_364701

theorem cert_377468 : Represents 3809 3807 :=
  segment 23 3809 3807 3832 1970 (by rfl) cert_341076

theorem cert_377545 : Represents 4062 3808 :=
  segment 76 4062 3808 4138 950 (by rfl) cert_292649

theorem cert_377735 : Represents 3872 2696 :=
  segment 190 3872 2696 4062 3808 (by rfl) cert_377545

theorem cert_377797 : Represents 3810 3808 :=
  segment 62 3810 3808 3872 2696 (by rfl) cert_377735

theorem cert_377801 : Represents 3811 3809 :=
  segment 3 3811 3809 3814 3784 (by rfl) cert_9561

theorem cert_377832 : Represents 3812 3810 :=
  segment 30 3812 3810 3842 2814 (by rfl) cert_342331

theorem cert_377873 : Represents 3902 736 :=
  segment 40 3902 736 3942 0 (by rfl) (zero_represents 3942)

theorem cert_377903 : Represents 3872 3842 :=
  segment 30 3872 3842 3902 736 (by rfl) cert_377873

theorem cert_377962 : Represents 3813 3811 :=
  segment 59 3813 3811 3872 3842 (by rfl) cert_377903

theorem cert_378019 : Represents 3814 3812 :=
  segment 56 3814 3812 3870 1424 (by rfl) cert_366439

theorem cert_378026 : Represents 4064 1274 :=
  segment 6 4064 1274 4070 208 (by rfl) cert_139910

theorem cert_378275 : Represents 3815 3813 :=
  segment 249 3815 3813 4064 1274 (by rfl) cert_378026

theorem cert_378330 : Represents 3816 3814 :=
  segment 54 3816 3814 3870 3592 (by rfl) cert_326212

theorem cert_378369 : Represents 3840 3328 :=
  segment 38 3840 3328 3878 2496 (by rfl) cert_369131

theorem cert_378392 : Represents 3817 3815 :=
  segment 23 3817 3815 3840 3328 (by rfl) cert_378369

theorem cert_378649 : Represents 155686 60914 :=
  segment 256 155686 60914 155942 0 (by rfl) (zero_represents 155942)

theorem cert_378905 : Represents 155430 3802 :=
  segment 256 155430 3802 155686 60914 (by rfl) cert_378649

theorem cert_379161 : Represents 155174 30506 :=
  segment 256 155174 30506 155430 3802 (by rfl) cert_378905

theorem cert_379417 : Represents 154918 54022 :=
  segment 256 154918 54022 155174 30506 (by rfl) cert_379161

theorem cert_379673 : Represents 154662 6632 :=
  segment 256 154662 6632 154918 54022 (by rfl) cert_379417

theorem cert_379929 : Represents 154406 69554 :=
  segment 256 154406 69554 154662 6632 (by rfl) cert_379673

theorem cert_380185 : Represents 154150 712 :=
  segment 256 154150 712 154406 69554 (by rfl) cert_379929

theorem cert_380441 : Represents 153894 53032 :=
  segment 256 153894 53032 154150 712 (by rfl) cert_380185

theorem cert_380697 : Represents 153638 15304 :=
  segment 256 153638 15304 153894 53032 (by rfl) cert_380441

theorem cert_380953 : Represents 153382 77440 :=
  segment 256 153382 77440 153638 15304 (by rfl) cert_380697

theorem cert_381209 : Represents 153126 94770 :=
  segment 256 153126 94770 153382 77440 (by rfl) cert_380953

theorem cert_381465 : Represents 152870 124616 :=
  segment 256 152870 124616 153126 94770 (by rfl) cert_381209

theorem cert_381721 : Represents 152614 38896 :=
  segment 256 152614 38896 152870 124616 (by rfl) cert_381465

theorem cert_381977 : Represents 152358 142554 :=
  segment 256 152358 142554 152614 38896 (by rfl) cert_381721

theorem cert_382233 : Represents 152102 91120 :=
  segment 256 152102 91120 152358 142554 (by rfl) cert_381977

theorem cert_382489 : Represents 151846 12090 :=
  segment 256 151846 12090 152102 91120 (by rfl) cert_382233

theorem cert_382745 : Represents 151590 137714 :=
  segment 256 151590 137714 151846 12090 (by rfl) cert_382489

theorem cert_383001 : Represents 151334 100226 :=
  segment 256 151334 100226 151590 137714 (by rfl) cert_382745

theorem cert_383257 : Represents 151078 71488 :=
  segment 256 151078 71488 151334 100226 (by rfl) cert_383001

theorem cert_383513 : Represents 150822 123134 :=
  segment 256 150822 123134 151078 71488 (by rfl) cert_383257

theorem cert_383769 : Represents 150566 10898 :=
  segment 256 150566 10898 150822 123134 (by rfl) cert_383513

theorem cert_384025 : Represents 150310 4936 :=
  segment 256 150310 4936 150566 10898 (by rfl) cert_383769

theorem cert_384281 : Represents 150054 100720 :=
  segment 256 150054 100720 150310 4936 (by rfl) cert_384025

theorem cert_384537 : Represents 149798 125422 :=
  segment 256 149798 125422 150054 100720 (by rfl) cert_384281

theorem cert_384793 : Represents 149542 77506 :=
  segment 256 149542 77506 149798 125422 (by rfl) cert_384537

theorem cert_385049 : Represents 149286 59048 :=
  segment 256 149286 59048 149542 77506 (by rfl) cert_384793

theorem cert_385305 : Represents 149030 42688 :=
  segment 256 149030 42688 149286 59048 (by rfl) cert_385049

theorem cert_385561 : Represents 148774 30032 :=
  segment 256 148774 30032 149030 42688 (by rfl) cert_385305

theorem cert_385817 : Represents 148518 85522 :=
  segment 256 148518 85522 148774 30032 (by rfl) cert_385561

theorem cert_386073 : Represents 148262 90530 :=
  segment 256 148262 90530 148518 85522 (by rfl) cert_385817

theorem cert_386329 : Represents 148006 132486 :=
  segment 256 148006 132486 148262 90530 (by rfl) cert_386073

theorem cert_386585 : Represents 147750 98928 :=
  segment 256 147750 98928 148006 132486 (by rfl) cert_386329

theorem cert_386841 : Represents 147494 32752 :=
  segment 256 147494 32752 147750 98928 (by rfl) cert_386585

theorem cert_387097 : Represents 147238 15822 :=
  segment 256 147238 15822 147494 32752 (by rfl) cert_386841

theorem cert_387353 : Represents 146982 99966 :=
  segment 256 146982 99966 147238 15822 (by rfl) cert_387097

theorem cert_387609 : Represents 146726 97930 :=
  segment 256 146726 97930 146982 99966 (by rfl) cert_387353

theorem cert_387865 : Represents 146470 96424 :=
  segment 256 146470 96424 146726 97930 (by rfl) cert_387609

theorem cert_388121 : Represents 146214 78262 :=
  segment 256 146214 78262 146470 96424 (by rfl) cert_387865

theorem cert_388377 : Represents 145958 86038 :=
  segment 256 145958 86038 146214 78262 (by rfl) cert_388121

theorem cert_388633 : Represents 145702 81430 :=
  segment 256 145702 81430 145958 86038 (by rfl) cert_388377

theorem cert_388889 : Represents 145446 96896 :=
  segment 256 145446 96896 145702 81430 (by rfl) cert_388633

theorem cert_389145 : Represents 145190 95056 :=
  segment 256 145190 95056 145446 96896 (by rfl) cert_388889

theorem cert_389401 : Represents 144934 54240 :=
  segment 256 144934 54240 145190 95056 (by rfl) cert_389145

theorem cert_389657 : Represents 144678 9664 :=
  segment 256 144678 9664 144934 54240 (by rfl) cert_389401

theorem cert_389913 : Represents 144422 92456 :=
  segment 256 144422 92456 144678 9664 (by rfl) cert_389657

theorem cert_390169 : Represents 144166 101968 :=
  segment 256 144166 101968 144422 92456 (by rfl) cert_389913

theorem cert_390425 : Represents 143910 3408 :=
  segment 256 143910 3408 144166 101968 (by rfl) cert_390169

theorem cert_390681 : Represents 143654 104688 :=
  segment 256 143654 104688 143910 3408 (by rfl) cert_390425

theorem cert_390937 : Represents 143398 48730 :=
  segment 256 143398 48730 143654 104688 (by rfl) cert_390681

theorem cert_391193 : Represents 143142 840 :=
  segment 256 143142 840 143398 48730 (by rfl) cert_390937

theorem cert_391449 : Represents 142886 39850 :=
  segment 256 142886 39850 143142 840 (by rfl) cert_391193

theorem cert_391705 : Represents 142630 100814 :=
  segment 256 142630 100814 142886 39850 (by rfl) cert_391449

theorem cert_391961 : Represents 142374 12914 :=
  segment 256 142374 12914 142630 100814 (by rfl) cert_391705

theorem cert_392217 : Represents 142118 104062 :=
  segment 256 142118 104062 142374 12914 (by rfl) cert_391961

theorem cert_392473 : Represents 141862 103208 :=
  segment 256 141862 103208 142118 104062 (by rfl) cert_392217

theorem cert_392729 : Represents 141606 131062 :=
  segment 256 141606 131062 141862 103208 (by rfl) cert_392473

theorem cert_392985 : Represents 141350 40424 :=
  segment 256 141350 40424 141606 131062 (by rfl) cert_392729

theorem cert_393241 : Represents 141094 133666 :=
  segment 256 141094 133666 141350 40424 (by rfl) cert_392985

theorem cert_393497 : Represents 140838 71314 :=
  segment 256 140838 71314 141094 133666 (by rfl) cert_393241

theorem cert_393753 : Represents 140582 92346 :=
  segment 256 140582 92346 140838 71314 (by rfl) cert_393497

theorem cert_394009 : Represents 140326 55314 :=
  segment 256 140326 55314 140582 92346 (by rfl) cert_393753

theorem cert_394265 : Represents 140070 36320 :=
  segment 256 140070 36320 140326 55314 (by rfl) cert_394009

theorem cert_394521 : Represents 139814 4664 :=
  segment 256 139814 4664 140070 36320 (by rfl) cert_394265

theorem cert_394777 : Represents 139558 9544 :=
  segment 256 139558 9544 139814 4664 (by rfl) cert_394521

theorem cert_395033 : Represents 139302 17376 :=
  segment 256 139302 17376 139558 9544 (by rfl) cert_394777

theorem cert_395289 : Represents 139046 49738 :=
  segment 256 139046 49738 139302 17376 (by rfl) cert_395033

theorem cert_395545 : Represents 138790 100392 :=
  segment 256 138790 100392 139046 49738 (by rfl) cert_395289

theorem cert_395801 : Represents 138534 105288 :=
  segment 256 138534 105288 138790 100392 (by rfl) cert_395545

theorem cert_396057 : Represents 138278 67202 :=
  segment 256 138278 67202 138534 105288 (by rfl) cert_395801

theorem cert_396313 : Represents 138022 114918 :=
  segment 256 138022 114918 138278 67202 (by rfl) cert_396057

theorem cert_396569 : Represents 137766 28728 :=
  segment 256 137766 28728 138022 114918 (by rfl) cert_396313

theorem cert_396825 : Represents 137510 90982 :=
  segment 256 137510 90982 137766 28728 (by rfl) cert_396569

theorem cert_397081 : Represents 137254 74898 :=
  segment 256 137254 74898 137510 90982 (by rfl) cert_396825

theorem cert_397337 : Represents 136998 55904 :=
  segment 256 136998 55904 137254 74898 (by rfl) cert_397081

theorem cert_397593 : Represents 136742 47638 :=
  segment 256 136742 47638 136998 55904 (by rfl) cert_397337

theorem cert_397849 : Represents 136486 83718 :=
  segment 256 136486 83718 136742 47638 (by rfl) cert_397593

theorem cert_398105 : Represents 136230 132394 :=
  segment 256 136230 132394 136486 83718 (by rfl) cert_397849

theorem cert_398361 : Represents 135974 127498 :=
  segment 256 135974 127498 136230 132394 (by rfl) cert_398105

theorem cert_398617 : Represents 135718 77806 :=
  segment 256 135718 77806 135974 127498 (by rfl) cert_398361

theorem cert_398873 : Represents 135462 95914 :=
  segment 256 135462 95914 135718 77806 (by rfl) cert_398617

theorem cert_399129 : Represents 135206 15944 :=
  segment 256 135206 15944 135462 95914 (by rfl) cert_398873

theorem cert_399385 : Represents 134950 59194 :=
  segment 256 134950 59194 135206 15944 (by rfl) cert_399129

theorem cert_399641 : Represents 134694 9890 :=
  segment 256 134694 9890 134950 59194 (by rfl) cert_399385

theorem cert_399897 : Represents 134438 25538 :=
  segment 256 134438 25538 134694 9890 (by rfl) cert_399641

theorem cert_400153 : Represents 134182 25994 :=
  segment 256 134182 25994 134438 25538 (by rfl) cert_399897

theorem cert_400409 : Represents 133926 49208 :=
  segment 256 133926 49208 134182 25994 (by rfl) cert_400153

theorem cert_400665 : Represents 133670 62242 :=
  segment 256 133670 62242 133926 49208 (by rfl) cert_400409

theorem cert_400921 : Represents 133414 49574 :=
  segment 256 133414 49574 133670 62242 (by rfl) cert_400665

theorem cert_401177 : Represents 133158 51448 :=
  segment 256 133158 51448 133414 49574 (by rfl) cert_400921

theorem cert_401433 : Represents 132902 49368 :=
  segment 256 132902 49368 133158 51448 (by rfl) cert_401177

theorem cert_401689 : Represents 132646 21112 :=
  segment 256 132646 21112 132902 49368 (by rfl) cert_401433

theorem cert_401945 : Represents 132390 20664 :=
  segment 256 132390 20664 132646 21112 (by rfl) cert_401689

theorem cert_402201 : Represents 132134 23256 :=
  segment 256 132134 23256 132390 20664 (by rfl) cert_401945

theorem cert_402457 : Represents 131878 4642 :=
  segment 256 131878 4642 132134 23256 (by rfl) cert_402201

theorem cert_402713 : Represents 131622 15560 :=
  segment 256 131622 15560 131878 4642 (by rfl) cert_402457

theorem cert_402969 : Represents 131366 67376 :=
  segment 256 131366 67376 131622 15560 (by rfl) cert_402713

theorem cert_403225 : Represents 131110 53638 :=
  segment 256 131110 53638 131366 67376 (by rfl) cert_402969

theorem cert_403481 : Represents 130854 104386 :=
  segment 256 130854 104386 131110 53638 (by rfl) cert_403225

theorem cert_403737 : Represents 130598 93720 :=
  segment 256 130598 93720 130854 104386 (by rfl) cert_403481

theorem cert_403993 : Represents 130342 60544 :=
  segment 256 130342 60544 130598 93720 (by rfl) cert_403737

theorem cert_404249 : Represents 130086 92216 :=
  segment 256 130086 92216 130342 60544 (by rfl) cert_403993

theorem cert_404505 : Represents 129830 125072 :=
  segment 256 129830 125072 130086 92216 (by rfl) cert_404249

theorem cert_404761 : Represents 129574 94650 :=
  segment 256 129574 94650 129830 125072 (by rfl) cert_404505

theorem cert_405017 : Represents 129318 49104 :=
  segment 256 129318 49104 129574 94650 (by rfl) cert_404761

theorem cert_405273 : Represents 129062 68502 :=
  segment 256 129062 68502 129318 49104 (by rfl) cert_405017

theorem cert_405529 : Represents 128806 97792 :=
  segment 256 128806 97792 129062 68502 (by rfl) cert_405273

theorem cert_405785 : Represents 128550 23842 :=
  segment 256 128550 23842 128806 97792 (by rfl) cert_405529

theorem cert_406041 : Represents 128294 118104 :=
  segment 256 128294 118104 128550 23842 (by rfl) cert_405785

theorem cert_406297 : Represents 128038 49610 :=
  segment 256 128038 49610 128294 118104 (by rfl) cert_406041

theorem cert_406553 : Represents 127782 110920 :=
  segment 256 127782 110920 128038 49610 (by rfl) cert_406297

theorem cert_406809 : Represents 127526 86918 :=
  segment 256 127526 86918 127782 110920 (by rfl) cert_406553

theorem cert_407065 : Represents 127270 20328 :=
  segment 256 127270 20328 127526 86918 (by rfl) cert_406809

theorem cert_407321 : Represents 127014 47488 :=
  segment 256 127014 47488 127270 20328 (by rfl) cert_407065

theorem cert_407577 : Represents 126758 114186 :=
  segment 256 126758 114186 127014 47488 (by rfl) cert_407321

theorem cert_407833 : Represents 126502 38784 :=
  segment 256 126502 38784 126758 114186 (by rfl) cert_407577

theorem cert_408089 : Represents 126246 31840 :=
  segment 256 126246 31840 126502 38784 (by rfl) cert_407833

theorem cert_408345 : Represents 125990 81426 :=
  segment 256 125990 81426 126246 31840 (by rfl) cert_408089

theorem cert_408601 : Represents 125734 104634 :=
  segment 256 125734 104634 125990 81426 (by rfl) cert_408345

theorem cert_408857 : Represents 125478 110486 :=
  segment 256 125478 110486 125734 104634 (by rfl) cert_408601

theorem cert_409113 : Represents 125222 107042 :=
  segment 256 125222 107042 125478 110486 (by rfl) cert_408857

theorem cert_409369 : Represents 124966 29096 :=
  segment 256 124966 29096 125222 107042 (by rfl) cert_409113

theorem cert_409625 : Represents 124710 480 :=
  segment 256 124710 480 124966 29096 (by rfl) cert_409369

theorem cert_409881 : Represents 124454 53584 :=
  segment 256 124454 53584 124710 480 (by rfl) cert_409625

theorem cert_410137 : Represents 124198 27992 :=
  segment 256 124198 27992 124454 53584 (by rfl) cert_409881

theorem cert_410393 : Represents 123942 42448 :=
  segment 256 123942 42448 124198 27992 (by rfl) cert_410137

theorem cert_410649 : Represents 123686 68312 :=
  segment 256 123686 68312 123942 42448 (by rfl) cert_410393

theorem cert_410905 : Represents 123430 11592 :=
  segment 256 123430 11592 123686 68312 (by rfl) cert_410649

theorem cert_411161 : Represents 123174 69306 :=
  segment 256 123174 69306 123430 11592 (by rfl) cert_410905

theorem cert_411417 : Represents 122918 62536 :=
  segment 256 122918 62536 123174 69306 (by rfl) cert_411161

theorem cert_411673 : Represents 122662 28608 :=
  segment 256 122662 28608 122918 62536 (by rfl) cert_411417

theorem cert_411929 : Represents 122406 109896 :=
  segment 256 122406 109896 122662 28608 (by rfl) cert_411673

theorem cert_412185 : Represents 122150 26666 :=
  segment 256 122150 26666 122406 109896 (by rfl) cert_411929

theorem cert_412441 : Represents 121894 49784 :=
  segment 256 121894 49784 122150 26666 (by rfl) cert_412185

theorem cert_412697 : Represents 121638 95296 :=
  segment 256 121638 95296 121894 49784 (by rfl) cert_412441

theorem cert_412953 : Represents 121382 98198 :=
  segment 256 121382 98198 121638 95296 (by rfl) cert_412697

theorem cert_413209 : Represents 121126 20064 :=
  segment 256 121126 20064 121382 98198 (by rfl) cert_412953

theorem cert_413465 : Represents 120870 70880 :=
  segment 256 120870 70880 121126 20064 (by rfl) cert_413209

theorem cert_413721 : Represents 120614 88086 :=
  segment 256 120614 88086 120870 70880 (by rfl) cert_413465

theorem cert_413977 : Represents 120358 42336 :=
  segment 256 120358 42336 120614 88086 (by rfl) cert_413721

theorem cert_414233 : Represents 120102 113406 :=
  segment 256 120102 113406 120358 42336 (by rfl) cert_413977

theorem cert_414489 : Represents 119846 83598 :=
  segment 256 119846 83598 120102 113406 (by rfl) cert_414233

theorem cert_414745 : Represents 119590 11930 :=
  segment 256 119590 11930 119846 83598 (by rfl) cert_414489

theorem cert_415001 : Represents 119334 35656 :=
  segment 256 119334 35656 119590 11930 (by rfl) cert_414745

theorem cert_415257 : Represents 119078 98054 :=
  segment 256 119078 98054 119334 35656 (by rfl) cert_415001

theorem cert_415513 : Represents 118822 37486 :=
  segment 256 118822 37486 119078 98054 (by rfl) cert_415257

theorem cert_415769 : Represents 118566 3442 :=
  segment 256 118566 3442 118822 37486 (by rfl) cert_415513

theorem cert_416025 : Represents 118310 21088 :=
  segment 256 118310 21088 118566 3442 (by rfl) cert_415769

theorem cert_416281 : Represents 118054 81482 :=
  segment 256 118054 81482 118310 21088 (by rfl) cert_416025

theorem cert_416537 : Represents 117798 59232 :=
  segment 256 117798 59232 118054 81482 (by rfl) cert_416281

theorem cert_416793 : Represents 117542 53142 :=
  segment 256 117542 53142 117798 59232 (by rfl) cert_416537

theorem cert_417049 : Represents 117286 18920 :=
  segment 256 117286 18920 117542 53142 (by rfl) cert_416793

theorem cert_417305 : Represents 117030 30288 :=
  segment 256 117030 30288 117286 18920 (by rfl) cert_417049

theorem cert_417561 : Represents 116774 552 :=
  segment 256 116774 552 117030 30288 (by rfl) cert_417305

theorem cert_417817 : Represents 116518 71422 :=
  segment 256 116518 71422 116774 552 (by rfl) cert_417561

theorem cert_418073 : Represents 116262 90882 :=
  segment 256 116262 90882 116518 71422 (by rfl) cert_417817

theorem cert_418329 : Represents 116006 39272 :=
  segment 256 116006 39272 116262 90882 (by rfl) cert_418073

theorem cert_418585 : Represents 115750 20626 :=
  segment 256 115750 20626 116006 39272 (by rfl) cert_418329

theorem cert_418841 : Represents 115494 13262 :=
  segment 256 115494 13262 115750 20626 (by rfl) cert_418585

theorem cert_419097 : Represents 115238 68280 :=
  segment 256 115238 68280 115494 13262 (by rfl) cert_418841

theorem cert_419353 : Represents 114982 104048 :=
  segment 256 114982 104048 115238 68280 (by rfl) cert_419097

theorem cert_419609 : Represents 114726 75248 :=
  segment 256 114726 75248 114982 104048 (by rfl) cert_419353

theorem cert_419865 : Represents 114470 53728 :=
  segment 256 114470 53728 114726 75248 (by rfl) cert_419609

theorem cert_420121 : Represents 114214 96344 :=
  segment 256 114214 96344 114470 53728 (by rfl) cert_419865

theorem cert_420377 : Represents 113958 62256 :=
  segment 256 113958 62256 114214 96344 (by rfl) cert_420121

theorem cert_420633 : Represents 113702 78558 :=
  segment 256 113702 78558 113958 62256 (by rfl) cert_420377

theorem cert_420889 : Represents 113446 66904 :=
  segment 256 113446 66904 113702 78558 (by rfl) cert_420633

theorem cert_421145 : Represents 113190 5342 :=
  segment 256 113190 5342 113446 66904 (by rfl) cert_420889

theorem cert_421401 : Represents 112934 22126 :=
  segment 256 112934 22126 113190 5342 (by rfl) cert_421145

theorem cert_421657 : Represents 112678 65946 :=
  segment 256 112678 65946 112934 22126 (by rfl) cert_421401

theorem cert_421913 : Represents 112422 99296 :=
  segment 256 112422 99296 112678 65946 (by rfl) cert_421657

theorem cert_422169 : Represents 112166 82216 :=
  segment 256 112166 82216 112422 99296 (by rfl) cert_421913

theorem cert_422425 : Represents 111910 96736 :=
  segment 256 111910 96736 112166 82216 (by rfl) cert_422169

theorem cert_422681 : Represents 111654 22896 :=
  segment 256 111654 22896 111910 96736 (by rfl) cert_422425

theorem cert_422937 : Represents 111398 18880 :=
  segment 256 111398 18880 111654 22896 (by rfl) cert_422681

theorem cert_423193 : Represents 111142 108702 :=
  segment 256 111142 108702 111398 18880 (by rfl) cert_422937

theorem cert_423449 : Represents 110886 58000 :=
  segment 256 110886 58000 111142 108702 (by rfl) cert_423193

theorem cert_423705 : Represents 110630 41296 :=
  segment 256 110630 41296 110886 58000 (by rfl) cert_423449

theorem cert_423961 : Represents 110374 13936 :=
  segment 256 110374 13936 110630 41296 (by rfl) cert_423705

theorem cert_424217 : Represents 110118 72730 :=
  segment 256 110118 72730 110374 13936 (by rfl) cert_423961

theorem cert_424473 : Represents 109862 31902 :=
  segment 256 109862 31902 110118 72730 (by rfl) cert_424217

theorem cert_424729 : Represents 109606 41936 :=
  segment 256 109606 41936 109862 31902 (by rfl) cert_424473

theorem cert_424985 : Represents 109350 45752 :=
  segment 256 109350 45752 109606 41936 (by rfl) cert_424729

theorem cert_425241 : Represents 109094 26306 :=
  segment 256 109094 26306 109350 45752 (by rfl) cert_424985

theorem cert_425497 : Represents 108838 98640 :=
  segment 256 108838 98640 109094 26306 (by rfl) cert_425241

theorem cert_425753 : Represents 108582 26290 :=
  segment 256 108582 26290 108838 98640 (by rfl) cert_425497

theorem cert_426009 : Represents 108326 48808 :=
  segment 256 108326 48808 108582 26290 (by rfl) cert_425753

theorem cert_426265 : Represents 108070 34328 :=
  segment 256 108070 34328 108326 48808 (by rfl) cert_426009

theorem cert_426521 : Represents 107814 79968 :=
  segment 256 107814 79968 108070 34328 (by rfl) cert_426265

theorem cert_426777 : Represents 107558 103090 :=
  segment 256 107558 103090 107814 79968 (by rfl) cert_426521

theorem cert_427033 : Represents 107302 45288 :=
  segment 256 107302 45288 107558 103090 (by rfl) cert_426777

theorem cert_427289 : Represents 107046 31712 :=
  segment 256 107046 31712 107302 45288 (by rfl) cert_427033

theorem cert_427545 : Represents 106790 64406 :=
  segment 256 106790 64406 107046 31712 (by rfl) cert_427289

theorem cert_427801 : Represents 106534 77776 :=
  segment 256 106534 77776 106790 64406 (by rfl) cert_427545

theorem cert_428057 : Represents 106278 50178 :=
  segment 256 106278 50178 106534 77776 (by rfl) cert_427801

theorem cert_428313 : Represents 106022 24982 :=
  segment 256 106022 24982 106278 50178 (by rfl) cert_428057

theorem cert_428569 : Represents 105766 26658 :=
  segment 256 105766 26658 106022 24982 (by rfl) cert_428313

theorem cert_428825 : Represents 105510 76888 :=
  segment 256 105510 76888 105766 26658 (by rfl) cert_428569

theorem cert_429081 : Represents 105254 75526 :=
  segment 256 105254 75526 105510 76888 (by rfl) cert_428825

theorem cert_429337 : Represents 104998 17566 :=
  segment 256 104998 17566 105254 75526 (by rfl) cert_429081

theorem cert_429593 : Represents 104742 37688 :=
  segment 256 104742 37688 104998 17566 (by rfl) cert_429337

theorem cert_429849 : Represents 104486 6200 :=
  segment 256 104486 6200 104742 37688 (by rfl) cert_429593

theorem cert_430105 : Represents 104230 51870 :=
  segment 256 104230 51870 104486 6200 (by rfl) cert_429849

theorem cert_430361 : Represents 103974 37162 :=
  segment 256 103974 37162 104230 51870 (by rfl) cert_430105

theorem cert_430617 : Represents 103718 25712 :=
  segment 256 103718 25712 103974 37162 (by rfl) cert_430361

theorem cert_430873 : Represents 103462 7752 :=
  segment 256 103462 7752 103718 25712 (by rfl) cert_430617

theorem cert_431129 : Represents 103206 82030 :=
  segment 256 103206 82030 103462 7752 (by rfl) cert_430873

theorem cert_431385 : Represents 102950 70878 :=
  segment 256 102950 70878 103206 82030 (by rfl) cert_431129

theorem cert_431641 : Represents 102694 12582 :=
  segment 256 102694 12582 102950 70878 (by rfl) cert_431385

theorem cert_431897 : Represents 102438 9362 :=
  segment 256 102438 9362 102694 12582 (by rfl) cert_431641

theorem cert_432153 : Represents 102182 8070 :=
  segment 256 102182 8070 102438 9362 (by rfl) cert_431897

theorem cert_432409 : Represents 101926 81144 :=
  segment 256 101926 81144 102182 8070 (by rfl) cert_432153

theorem cert_432665 : Represents 101670 56008 :=
  segment 256 101670 56008 101926 81144 (by rfl) cert_432409

theorem cert_432921 : Represents 101414 33818 :=
  segment 256 101414 33818 101670 56008 (by rfl) cert_432665

theorem cert_433177 : Represents 101158 886 :=
  segment 256 101158 886 101414 33818 (by rfl) cert_432921

theorem cert_433433 : Represents 100902 38478 :=
  segment 256 100902 38478 101158 886 (by rfl) cert_433177

theorem cert_433689 : Represents 100646 38608 :=
  segment 256 100646 38608 100902 38478 (by rfl) cert_433433

theorem cert_433945 : Represents 100390 57818 :=
  segment 256 100390 57818 100646 38608 (by rfl) cert_433689

theorem cert_434201 : Represents 100134 92446 :=
  segment 256 100134 92446 100390 57818 (by rfl) cert_433945

theorem cert_434457 : Represents 99878 10576 :=
  segment 256 99878 10576 100134 92446 (by rfl) cert_434201

theorem cert_434713 : Represents 99622 36336 :=
  segment 256 99622 36336 99878 10576 (by rfl) cert_434457

theorem cert_434969 : Represents 99366 11520 :=
  segment 256 99366 11520 99622 36336 (by rfl) cert_434713

theorem cert_435225 : Represents 99110 9712 :=
  segment 256 99110 9712 99366 11520 (by rfl) cert_434969

theorem cert_435481 : Represents 98854 9880 :=
  segment 256 98854 9880 99110 9712 (by rfl) cert_435225

theorem cert_435737 : Represents 98598 78462 :=
  segment 256 98598 78462 98854 9880 (by rfl) cert_435481

theorem cert_435993 : Represents 98342 65272 :=
  segment 256 98342 65272 98598 78462 (by rfl) cert_435737

theorem cert_436249 : Represents 98086 72234 :=
  segment 256 98086 72234 98342 65272 (by rfl) cert_435993

theorem cert_436505 : Represents 97830 47688 :=
  segment 256 97830 47688 98086 72234 (by rfl) cert_436249

theorem cert_436761 : Represents 97574 53990 :=
  segment 256 97574 53990 97830 47688 (by rfl) cert_436505

theorem cert_437017 : Represents 97318 72208 :=
  segment 256 97318 72208 97574 53990 (by rfl) cert_436761

theorem cert_437273 : Represents 97062 31528 :=
  segment 256 97062 31528 97318 72208 (by rfl) cert_437017

theorem cert_437529 : Represents 96806 55734 :=
  segment 256 96806 55734 97062 31528 (by rfl) cert_437273

theorem cert_437785 : Represents 96550 25928 :=
  segment 256 96550 25928 96806 55734 (by rfl) cert_437529

theorem cert_438041 : Represents 96294 66368 :=
  segment 256 96294 66368 96550 25928 (by rfl) cert_437785

theorem cert_438297 : Represents 96038 45656 :=
  segment 256 96038 45656 96294 66368 (by rfl) cert_438041

theorem cert_438553 : Represents 95782 89672 :=
  segment 256 95782 89672 96038 45656 (by rfl) cert_438297

theorem cert_438809 : Represents 95526 624 :=
  segment 256 95526 624 95782 89672 (by rfl) cert_438553

theorem cert_439065 : Represents 95270 85048 :=
  segment 256 95270 85048 95526 624 (by rfl) cert_438809

theorem cert_439321 : Represents 95014 92382 :=
  segment 256 95014 92382 95270 85048 (by rfl) cert_439065

theorem cert_439577 : Represents 94758 15274 :=
  segment 256 94758 15274 95014 92382 (by rfl) cert_439321

theorem cert_439833 : Represents 94502 40326 :=
  segment 256 94502 40326 94758 15274 (by rfl) cert_439577

theorem cert_440089 : Represents 94246 88874 :=
  segment 256 94246 88874 94502 40326 (by rfl) cert_439833

theorem cert_440345 : Represents 93990 85734 :=
  segment 256 93990 85734 94246 88874 (by rfl) cert_440089

theorem cert_440601 : Represents 93734 70910 :=
  segment 256 93734 70910 93990 85734 (by rfl) cert_440345

theorem cert_440857 : Represents 93478 85704 :=
  segment 256 93478 85704 93734 70910 (by rfl) cert_440601

theorem cert_441113 : Represents 93222 40374 :=
  segment 256 93222 40374 93478 85704 (by rfl) cert_440857

theorem cert_441369 : Represents 92966 59122 :=
  segment 256 92966 59122 93222 40374 (by rfl) cert_441113

theorem cert_441625 : Represents 92710 55320 :=
  segment 256 92710 55320 92966 59122 (by rfl) cert_441369

theorem cert_441881 : Represents 92454 33784 :=
  segment 256 92454 33784 92710 55320 (by rfl) cert_441625

theorem cert_442137 : Represents 92198 76288 :=
  segment 256 92198 76288 92454 33784 (by rfl) cert_441881

theorem cert_442393 : Represents 91942 24160 :=
  segment 256 91942 24160 92198 76288 (by rfl) cert_442137

theorem cert_442649 : Represents 91686 72722 :=
  segment 256 91686 72722 91942 24160 (by rfl) cert_442393

theorem cert_442905 : Represents 91430 12104 :=
  segment 256 91430 12104 91686 72722 (by rfl) cert_442649

theorem cert_443161 : Represents 91174 52826 :=
  segment 256 91174 52826 91430 12104 (by rfl) cert_442905

theorem cert_443417 : Represents 90918 77618 :=
  segment 256 90918 77618 91174 52826 (by rfl) cert_443161

theorem cert_443673 : Represents 90662 23424 :=
  segment 256 90662 23424 90918 77618 (by rfl) cert_443417

theorem cert_443929 : Represents 90406 66174 :=
  segment 256 90406 66174 90662 23424 (by rfl) cert_443673

theorem cert_444185 : Represents 90150 31928 :=
  segment 256 90150 31928 90406 66174 (by rfl) cert_443929

theorem cert_444441 : Represents 89894 36712 :=
  segment 256 89894 36712 90150 31928 (by rfl) cert_444185

theorem cert_444697 : Represents 89638 89424 :=
  segment 256 89638 89424 89894 36712 (by rfl) cert_444441

theorem cert_444953 : Represents 89382 24218 :=
  segment 256 89382 24218 89638 89424 (by rfl) cert_444697

theorem cert_445209 : Represents 89126 15238 :=
  segment 256 89126 15238 89382 24218 (by rfl) cert_444953

theorem cert_445465 : Represents 88870 61776 :=
  segment 256 88870 61776 89126 15238 (by rfl) cert_445209

theorem cert_445721 : Represents 88614 37416 :=
  segment 256 88614 37416 88870 61776 (by rfl) cert_445465

theorem cert_445977 : Represents 88358 55222 :=
  segment 256 88358 55222 88614 37416 (by rfl) cert_445721

theorem cert_446233 : Represents 88102 19264 :=
  segment 256 88102 19264 88358 55222 (by rfl) cert_445977

theorem cert_446489 : Represents 87846 42464 :=
  segment 256 87846 42464 88102 19264 (by rfl) cert_446233

theorem cert_446745 : Represents 87590 83746 :=
  segment 256 87590 83746 87846 42464 (by rfl) cert_446489

theorem cert_447001 : Represents 87334 42270 :=
  segment 256 87334 42270 87590 83746 (by rfl) cert_446745

theorem cert_447257 : Represents 87078 24354 :=
  segment 256 87078 24354 87334 42270 (by rfl) cert_447001

theorem cert_447513 : Represents 86822 78318 :=
  segment 256 86822 78318 87078 24354 (by rfl) cert_447257

theorem cert_447769 : Represents 86566 18046 :=
  segment 256 86566 18046 86822 78318 (by rfl) cert_447513

theorem cert_448025 : Represents 86310 46778 :=
  segment 256 86310 46778 86566 18046 (by rfl) cert_447769

theorem cert_448281 : Represents 86054 38990 :=
  segment 256 86054 38990 86310 46778 (by rfl) cert_448025

theorem cert_448537 : Represents 85798 81150 :=
  segment 256 85798 81150 86054 38990 (by rfl) cert_448281

theorem cert_448793 : Represents 85542 48518 :=
  segment 256 85542 48518 85798 81150 (by rfl) cert_448537

theorem cert_449049 : Represents 85286 4110 :=
  segment 256 85286 4110 85542 48518 (by rfl) cert_448793

theorem cert_449305 : Represents 85030 58424 :=
  segment 256 85030 58424 85286 4110 (by rfl) cert_449049

theorem cert_449561 : Represents 84774 59654 :=
  segment 256 84774 59654 85030 58424 (by rfl) cert_449305

theorem cert_449817 : Represents 84518 35032 :=
  segment 256 84518 35032 84774 59654 (by rfl) cert_449561

theorem cert_450073 : Represents 84262 7952 :=
  segment 256 84262 7952 84518 35032 (by rfl) cert_449817

theorem cert_450329 : Represents 84006 65640 :=
  segment 256 84006 65640 84262 7952 (by rfl) cert_450073

theorem cert_450585 : Represents 83750 48534 :=
  segment 256 83750 48534 84006 65640 (by rfl) cert_450329

theorem cert_450841 : Represents 83494 47688 :=
  segment 256 83494 47688 83750 48534 (by rfl) cert_450585

theorem cert_451097 : Represents 83238 29032 :=
  segment 256 83238 29032 83494 47688 (by rfl) cert_450841

theorem cert_451353 : Represents 82982 28112 :=
  segment 256 82982 28112 83238 29032 (by rfl) cert_451097

theorem cert_451609 : Represents 82726 54806 :=
  segment 256 82726 54806 82982 28112 (by rfl) cert_451353

theorem cert_451865 : Represents 82470 20642 :=
  segment 256 82470 20642 82726 54806 (by rfl) cert_451609

theorem cert_452121 : Represents 82214 48018 :=
  segment 256 82214 48018 82470 20642 (by rfl) cert_451865

theorem cert_452377 : Represents 81958 31622 :=
  segment 256 81958 31622 82214 48018 (by rfl) cert_452121

theorem cert_452633 : Represents 81702 58600 :=
  segment 256 81702 58600 81958 31622 (by rfl) cert_452377

theorem cert_452889 : Represents 81446 1752 :=
  segment 256 81446 1752 81702 58600 (by rfl) cert_452633

theorem cert_453145 : Represents 81190 28254 :=
  segment 256 81190 28254 81446 1752 (by rfl) cert_452889

theorem cert_453401 : Represents 80934 56854 :=
  segment 256 80934 56854 81190 28254 (by rfl) cert_453145

theorem cert_453657 : Represents 80678 45536 :=
  segment 256 80678 45536 80934 56854 (by rfl) cert_453401

theorem cert_453913 : Represents 80422 14312 :=
  segment 256 80422 14312 80678 45536 (by rfl) cert_453657

theorem cert_454169 : Represents 80166 71768 :=
  segment 256 80166 71768 80422 14312 (by rfl) cert_453913

theorem cert_454425 : Represents 79910 64426 :=
  segment 256 79910 64426 80166 71768 (by rfl) cert_454169

theorem cert_454681 : Represents 79654 74472 :=
  segment 256 79654 74472 79910 64426 (by rfl) cert_454425

theorem cert_454937 : Represents 79398 45038 :=
  segment 256 79398 45038 79654 74472 (by rfl) cert_454681

theorem cert_455193 : Represents 79142 74626 :=
  segment 256 79142 74626 79398 45038 (by rfl) cert_454937

theorem cert_455449 : Represents 78886 1802 :=
  segment 256 78886 1802 79142 74626 (by rfl) cert_455193

theorem cert_455705 : Represents 78630 4280 :=
  segment 256 78630 4280 78886 1802 (by rfl) cert_455449

theorem cert_455961 : Represents 78374 53944 :=
  segment 256 78374 53944 78630 4280 (by rfl) cert_455705

theorem cert_456217 : Represents 78118 67168 :=
  segment 256 78118 67168 78374 53944 (by rfl) cert_455961

theorem cert_456473 : Represents 77862 39096 :=
  segment 256 77862 39096 78118 67168 (by rfl) cert_456217

theorem cert_456729 : Represents 77606 62106 :=
  segment 256 77606 62106 77862 39096 (by rfl) cert_456473

theorem cert_456985 : Represents 77350 49046 :=
  segment 256 77350 49046 77606 62106 (by rfl) cert_456729

theorem cert_457241 : Represents 77094 6082 :=
  segment 256 77094 6082 77350 49046 (by rfl) cert_456985

theorem cert_457497 : Represents 76838 27910 :=
  segment 256 76838 27910 77094 6082 (by rfl) cert_457241

theorem cert_457753 : Represents 76582 17200 :=
  segment 256 76582 17200 76838 27910 (by rfl) cert_457497

theorem cert_458009 : Represents 76326 45958 :=
  segment 256 76326 45958 76582 17200 (by rfl) cert_457753

theorem cert_458265 : Represents 76070 16384 :=
  segment 256 76070 16384 76326 45958 (by rfl) cert_458009

theorem cert_458521 : Represents 75814 21010 :=
  segment 256 75814 21010 76070 16384 (by rfl) cert_458265

theorem cert_458777 : Represents 75558 52320 :=
  segment 256 75558 52320 75814 21010 (by rfl) cert_458521

theorem cert_459033 : Represents 75302 31694 :=
  segment 256 75302 31694 75558 52320 (by rfl) cert_458777

theorem cert_459289 : Represents 75046 48224 :=
  segment 256 75046 48224 75302 31694 (by rfl) cert_459033

theorem cert_459545 : Represents 74790 2474 :=
  segment 256 74790 2474 75046 48224 (by rfl) cert_459289

theorem cert_459801 : Represents 74534 13904 :=
  segment 256 74534 13904 74790 2474 (by rfl) cert_459545

theorem cert_460057 : Represents 74278 64422 :=
  segment 256 74278 64422 74534 13904 (by rfl) cert_459801

theorem cert_460313 : Represents 74022 47538 :=
  segment 256 74022 47538 74278 64422 (by rfl) cert_460057

theorem cert_460569 : Represents 73766 40504 :=
  segment 256 73766 40504 74022 47538 (by rfl) cert_460313

theorem cert_460825 : Represents 73510 60866 :=
  segment 256 73510 60866 73766 40504 (by rfl) cert_460569

theorem cert_461081 : Represents 73254 28518 :=
  segment 256 73254 28518 73510 60866 (by rfl) cert_460825

theorem cert_461337 : Represents 72998 45864 :=
  segment 256 72998 45864 73254 28518 (by rfl) cert_461081

theorem cert_461593 : Represents 72742 22352 :=
  segment 256 72742 22352 72998 45864 (by rfl) cert_461337

theorem cert_461849 : Represents 72486 45726 :=
  segment 256 72486 45726 72742 22352 (by rfl) cert_461593

theorem cert_462105 : Represents 72230 19128 :=
  segment 256 72230 19128 72486 45726 (by rfl) cert_461849

theorem cert_462361 : Represents 71974 10242 :=
  segment 256 71974 10242 72230 19128 (by rfl) cert_462105

theorem cert_462617 : Represents 71718 42762 :=
  segment 256 71718 42762 71974 10242 (by rfl) cert_462361

theorem cert_462873 : Represents 71462 26752 :=
  segment 256 71462 26752 71718 42762 (by rfl) cert_462617

theorem cert_463129 : Represents 71206 23936 :=
  segment 256 71206 23936 71462 26752 (by rfl) cert_462873

theorem cert_463385 : Represents 70950 35920 :=
  segment 256 70950 35920 71206 23936 (by rfl) cert_463129

theorem cert_463641 : Represents 70694 34766 :=
  segment 256 70694 34766 70950 35920 (by rfl) cert_463385

theorem cert_463897 : Represents 70438 3150 :=
  segment 256 70438 3150 70694 34766 (by rfl) cert_463641

theorem cert_464153 : Represents 70182 42184 :=
  segment 256 70182 42184 70438 3150 (by rfl) cert_463897

theorem cert_464409 : Represents 69926 31560 :=
  segment 256 69926 31560 70182 42184 (by rfl) cert_464153

theorem cert_464665 : Represents 69670 64802 :=
  segment 256 69670 64802 69926 31560 (by rfl) cert_464409

theorem cert_464921 : Represents 69414 43816 :=
  segment 256 69414 43816 69670 64802 (by rfl) cert_464665

theorem cert_465177 : Represents 69158 36002 :=
  segment 256 69158 36002 69414 43816 (by rfl) cert_464921

theorem cert_465433 : Represents 68902 24998 :=
  segment 256 68902 24998 69158 36002 (by rfl) cert_465177

theorem cert_465689 : Represents 68646 30618 :=
  segment 256 68646 30618 68902 24998 (by rfl) cert_465433

theorem cert_465945 : Represents 68390 64918 :=
  segment 256 68390 64918 68646 30618 (by rfl) cert_465689

theorem cert_466201 : Represents 68134 28000 :=
  segment 256 68134 28000 68390 64918 (by rfl) cert_465945

theorem cert_466457 : Represents 67878 16462 :=
  segment 256 67878 16462 68134 28000 (by rfl) cert_466201

theorem cert_466713 : Represents 67622 51130 :=
  segment 256 67622 51130 67878 16462 (by rfl) cert_466457

theorem cert_466969 : Represents 67366 2946 :=
  segment 256 67366 2946 67622 51130 (by rfl) cert_466713

theorem cert_467225 : Represents 67110 27736 :=
  segment 256 67110 27736 67366 2946 (by rfl) cert_466969

theorem cert_467481 : Represents 66854 25474 :=
  segment 256 66854 25474 67110 27736 (by rfl) cert_467225

theorem cert_467737 : Represents 66598 39296 :=
  segment 256 66598 39296 66854 25474 (by rfl) cert_467481

theorem cert_467993 : Represents 66342 11264 :=
  segment 256 66342 11264 66598 39296 (by rfl) cert_467737

theorem cert_468249 : Represents 66086 39776 :=
  segment 256 66086 39776 66342 11264 (by rfl) cert_467993

theorem cert_468505 : Represents 65830 21472 :=
  segment 256 65830 21472 66086 39776 (by rfl) cert_468249

theorem cert_468761 : Represents 65574 11410 :=
  segment 256 65574 11410 65830 21472 (by rfl) cert_468505

theorem cert_469017 : Represents 65318 29738 :=
  segment 256 65318 29738 65574 11410 (by rfl) cert_468761

theorem cert_469273 : Represents 65062 52686 :=
  segment 256 65062 52686 65318 29738 (by rfl) cert_469017

theorem cert_469529 : Represents 64806 9762 :=
  segment 256 64806 9762 65062 52686 (by rfl) cert_469273

theorem cert_469785 : Represents 64550 51522 :=
  segment 256 64550 51522 64806 9762 (by rfl) cert_469529

theorem cert_470041 : Represents 64294 62506 :=
  segment 256 64294 62506 64550 51522 (by rfl) cert_469785

theorem cert_470297 : Represents 64038 63080 :=
  segment 256 64038 63080 64294 62506 (by rfl) cert_470041

theorem cert_470553 : Represents 63782 51264 :=
  segment 256 63782 51264 64038 63080 (by rfl) cert_470297

theorem cert_470809 : Represents 63526 19824 :=
  segment 256 63526 19824 63782 51264 (by rfl) cert_470553

theorem cert_471065 : Represents 63270 30920 :=
  segment 256 63270 30920 63526 19824 (by rfl) cert_470809

theorem cert_471321 : Represents 63014 51222 :=
  segment 256 63014 51222 63270 30920 (by rfl) cert_471065

theorem cert_471577 : Represents 62758 46408 :=
  segment 256 62758 46408 63014 51222 (by rfl) cert_471321

theorem cert_471833 : Represents 62502 12578 :=
  segment 256 62502 12578 62758 46408 (by rfl) cert_471577

theorem cert_472089 : Represents 62246 50470 :=
  segment 256 62246 50470 62502 12578 (by rfl) cert_471833

theorem cert_472345 : Represents 61990 536 :=
  segment 256 61990 536 62246 50470 (by rfl) cert_472089

theorem cert_472601 : Represents 61734 9198 :=
  segment 256 61734 9198 61990 536 (by rfl) cert_472345

theorem cert_472857 : Represents 61478 56574 :=
  segment 256 61478 56574 61734 9198 (by rfl) cert_472601

theorem cert_473113 : Represents 61222 56334 :=
  segment 256 61222 56334 61478 56574 (by rfl) cert_472857

theorem cert_473369 : Represents 60966 11008 :=
  segment 256 60966 11008 61222 56334 (by rfl) cert_473113

theorem cert_473625 : Represents 60710 51606 :=
  segment 256 60710 51606 60966 11008 (by rfl) cert_473369

theorem cert_473881 : Represents 60454 41666 :=
  segment 256 60454 41666 60710 51606 (by rfl) cert_473625

theorem cert_474137 : Represents 60198 26186 :=
  segment 256 60198 26186 60454 41666 (by rfl) cert_473881

theorem cert_474393 : Represents 59942 11448 :=
  segment 256 59942 11448 60198 26186 (by rfl) cert_474137

theorem cert_474649 : Represents 59686 46392 :=
  segment 256 59686 46392 59942 11448 (by rfl) cert_474393

theorem cert_474905 : Represents 59430 25176 :=
  segment 256 59430 25176 59686 46392 (by rfl) cert_474649

theorem cert_475161 : Represents 59174 52800 :=
  segment 256 59174 52800 59430 25176 (by rfl) cert_474905

theorem cert_475417 : Represents 58918 3408 :=
  segment 256 58918 3408 59174 52800 (by rfl) cert_475161

theorem cert_475673 : Represents 58662 47416 :=
  segment 256 58662 47416 58918 3408 (by rfl) cert_475417

theorem cert_475929 : Represents 58406 10592 :=
  segment 256 58406 10592 58662 47416 (by rfl) cert_475673

theorem cert_476185 : Represents 58150 35264 :=
  segment 256 58150 35264 58406 10592 (by rfl) cert_475929

theorem cert_476441 : Represents 57894 15048 :=
  segment 256 57894 15048 58150 35264 (by rfl) cert_476185

theorem cert_476697 : Represents 57638 15810 :=
  segment 256 57638 15810 57894 15048 (by rfl) cert_476441

theorem cert_476953 : Represents 57382 7240 :=
  segment 256 57382 7240 57638 15810 (by rfl) cert_476697

theorem cert_477209 : Represents 57126 7128 :=
  segment 256 57126 7128 57382 7240 (by rfl) cert_476953

theorem cert_477465 : Represents 56870 35896 :=
  segment 256 56870 35896 57126 7128 (by rfl) cert_477209

theorem cert_477721 : Represents 56614 4922 :=
  segment 256 56614 4922 56870 35896 (by rfl) cert_477465

theorem cert_477977 : Represents 56358 54082 :=
  segment 256 56358 54082 56614 4922 (by rfl) cert_477721

theorem cert_478233 : Represents 56102 45830 :=
  segment 256 56102 45830 56358 54082 (by rfl) cert_477977

theorem cert_478489 : Represents 55846 49066 :=
  segment 256 55846 49066 56102 45830 (by rfl) cert_478233

end Erdos261Finite
