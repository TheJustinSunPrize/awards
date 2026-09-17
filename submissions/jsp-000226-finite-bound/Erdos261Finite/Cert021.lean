import Erdos261Finite.Cert020

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace Erdos261Finite

theorem cert_647689 : Represents 5248 4546 :=
  segment 32 5248 4546 5280 2626 (by rfl) cert_647657

theorem cert_647705 : Represents 5232 3786 :=
  segment 16 5232 3786 5248 4546 (by rfl) cert_647689

theorem cert_647815 : Represents 5122 1798 :=
  segment 110 5122 1798 5232 3786 (by rfl) cert_647705

theorem cert_647875 : Represents 5062 512 :=
  segment 60 5062 512 5122 1798 (by rfl) cert_647815

theorem cert_647977 : Represents 4960 2114 :=
  segment 102 4960 2114 5062 512 (by rfl) cert_647875

theorem cert_648027 : Represents 4910 816 :=
  segment 50 4910 816 4960 2114 (by rfl) cert_647977

theorem cert_648127 : Represents 4810 54 :=
  segment 100 4810 54 4910 816 (by rfl) cert_648027

theorem cert_648224 : Represents 4713 4711 :=
  segment 97 4713 4711 4810 54 (by rfl) cert_648127

theorem cert_648239 : Represents 4714 4712 :=
  segment 14 4714 4712 4728 626 (by rfl) cert_631786

theorem cert_648259 : Represents 4715 4713 :=
  segment 19 4715 4713 4734 1552 (by rfl) cert_641014

theorem cert_648344 : Represents 4716 4714 :=
  segment 84 4716 4714 4800 2474 (by rfl) cert_574561

theorem cert_648393 : Represents 4872 2520 :=
  segment 48 4872 2520 4920 754 (by rfl) cert_633078

theorem cert_648548 : Represents 4717 4715 :=
  segment 155 4717 4715 4872 2520 (by rfl) cert_648393

theorem cert_648569 : Represents 4718 4716 :=
  segment 20 4718 4716 4738 1030 (by rfl) cert_593091

theorem cert_648602 : Represents 4872 4416 :=
  segment 32 4872 4416 4904 1810 (by rfl) cert_591859

theorem cert_648755 : Represents 4719 4717 :=
  segment 153 4719 4717 4872 4416 (by rfl) cert_648602

theorem cert_648884 : Represents 4720 4718 :=
  segment 128 4720 4718 4848 2280 (by rfl) cert_646101

theorem cert_648956 : Represents 4721 4719 :=
  segment 71 4721 4719 4792 4594 (by rfl) cert_641835

theorem cert_649043 : Represents 4722 4720 :=
  segment 86 4722 4720 4808 4394 (by rfl) cert_574553

theorem cert_649164 : Represents 4902 4392 :=
  segment 120 4902 4392 5022 2152 (by rfl) cert_591741

theorem cert_649343 : Represents 4723 4721 :=
  segment 179 4723 4721 4902 4392 (by rfl) cert_649164

theorem cert_649358 : Represents 4724 4722 :=
  segment 14 4724 4722 4738 766 (by rfl) cert_604195

theorem cert_649394 : Represents 4725 4723 :=
  segment 35 4725 4723 4760 1088 (by rfl) cert_600670

theorem cert_649403 : Represents 4864 1538 :=
  segment 8 4864 1538 4872 4416 (by rfl) cert_648602

theorem cert_649541 : Represents 4726 4724 :=
  segment 138 4726 4724 4864 1538 (by rfl) cert_649403

theorem cert_649549 : Represents 4727 4725 :=
  segment 7 4727 4725 4734 4224 (by rfl) cert_573817

theorem cert_649558 : Represents 4728 4726 :=
  segment 8 4728 4726 4736 3714 (by rfl) cert_640696

theorem cert_649564 : Represents 4729 4727 :=
  segment 5 4729 4727 4734 4608 (by rfl) cert_638642

theorem cert_649611 : Represents 4730 4728 :=
  segment 46 4730 4728 4776 3466 (by rfl) cert_634092

theorem cert_649624 : Represents 5026 4670 :=
  segment 12 5026 4670 5038 2520 (by rfl) cert_645558

theorem cert_649762 : Represents 4888 1562 :=
  segment 138 4888 1562 5026 4670 (by rfl) cert_649624

theorem cert_649919 : Represents 4731 4729 :=
  segment 157 4731 4729 4888 1562 (by rfl) cert_649762

theorem cert_649940 : Represents 4732 4730 :=
  segment 20 4732 4730 4752 3946 (by rfl) cert_604181

theorem cert_649974 : Represents 4733 4731 :=
  segment 33 4733 4731 4766 2784 (by rfl) cert_613682

theorem cert_649991 : Represents 4734 4732 :=
  segment 16 4734 4732 4750 3624 (by rfl) cert_569289

theorem cert_650070 : Represents 8802 8382 :=
  segment 78 8802 8382 8880 2570 (by rfl) cert_525455

theorem cert_650232 : Represents 8640 8610 :=
  segment 162 8640 8610 8802 8382 (by rfl) cert_650070

theorem cert_650264 : Represents 8608 5658 :=
  segment 32 8608 5658 8640 8610 (by rfl) cert_650232

theorem cert_650304 : Represents 8568 506 :=
  segment 40 8568 506 8608 5658 (by rfl) cert_650264

theorem cert_650360 : Represents 8512 2082 :=
  segment 56 8512 2082 8568 506 (by rfl) cert_650304

theorem cert_650392 : Represents 8480 8128 :=
  segment 32 8480 8128 8512 2082 (by rfl) cert_650360

theorem cert_650448 : Represents 8424 2474 :=
  segment 56 8424 2474 8480 8128 (by rfl) cert_650392

theorem cert_650704 : Represents 8168 4074 :=
  segment 256 8168 4074 8424 2474 (by rfl) cert_650448

theorem cert_650710 : Represents 8162 7462 :=
  segment 6 8162 7462 8168 4074 (by rfl) cert_650704

theorem cert_650730 : Represents 8142 8112 :=
  segment 20 8142 8112 8162 7462 (by rfl) cert_650710

theorem cert_650738 : Represents 8134 1176 :=
  segment 8 8134 1176 8142 8112 (by rfl) cert_650730

theorem cert_650928 : Represents 7944 6922 :=
  segment 190 7944 6922 8134 1176 (by rfl) cert_650738

theorem cert_650966 : Represents 7906 4038 :=
  segment 38 7906 4038 7944 6922 (by rfl) cert_650928

theorem cert_651032 : Represents 7840 4610 :=
  segment 66 7840 4610 7906 4038 (by rfl) cert_650966

theorem cert_651088 : Represents 7784 7768 :=
  segment 56 7784 7768 7840 4610 (by rfl) cert_651032

theorem cert_651160 : Represents 7712 1880 :=
  segment 72 7712 1880 7784 7768 (by rfl) cert_651088

theorem cert_651224 : Represents 7648 2330 :=
  segment 64 7648 2330 7712 1880 (by rfl) cert_651160

theorem cert_651262 : Represents 7610 6158 :=
  segment 38 7610 6158 7648 2330 (by rfl) cert_651224

theorem cert_651352 : Represents 7520 7328 :=
  segment 90 7520 7328 7610 6158 (by rfl) cert_651262

theorem cert_651354 : Represents 7518 3712 :=
  segment 2 7518 3712 7520 7328 (by rfl) cert_651352

theorem cert_651362 : Represents 7510 3272 :=
  segment 8 7510 3272 7518 3712 (by rfl) cert_651354

theorem cert_651586 : Represents 7286 5808 :=
  segment 224 7286 5808 7510 3272 (by rfl) cert_651362

theorem cert_651638 : Represents 7234 2470 :=
  segment 52 7234 2470 7286 5808 (by rfl) cert_651586

theorem cert_651670 : Represents 7202 5830 :=
  segment 32 7202 5830 7234 2470 (by rfl) cert_651638

theorem cert_651830 : Represents 7042 5886 :=
  segment 160 7042 5886 7202 5830 (by rfl) cert_651670

theorem cert_651862 : Represents 7010 6086 :=
  segment 32 7010 6086 7042 5886 (by rfl) cert_651830

theorem cert_651864 : Represents 7008 5026 :=
  segment 2 7008 5026 7010 6086 (by rfl) cert_651862

theorem cert_651920 : Represents 6952 3736 :=
  segment 56 6952 3736 7008 5026 (by rfl) cert_651864

theorem cert_651958 : Represents 6914 1414 :=
  segment 38 6914 1414 6952 3736 (by rfl) cert_651920

theorem cert_651970 : Represents 6902 4096 :=
  segment 12 6902 4096 6914 1414 (by rfl) cert_651958

theorem cert_652050 : Represents 6822 2792 :=
  segment 80 6822 2792 6902 4096 (by rfl) cert_651970

theorem cert_652290 : Represents 6582 968 :=
  segment 240 6582 968 6822 2792 (by rfl) cert_652050

theorem cert_652336 : Represents 6536 1074 :=
  segment 46 6536 1074 6582 968 (by rfl) cert_652290

theorem cert_652400 : Represents 6472 704 :=
  segment 64 6472 704 6536 1074 (by rfl) cert_652336

theorem cert_652494 : Represents 6378 1302 :=
  segment 94 6378 1302 6472 704 (by rfl) cert_652400

theorem cert_652514 : Represents 6358 480 :=
  segment 20 6358 480 6378 1302 (by rfl) cert_652494

theorem cert_652528 : Represents 6344 434 :=
  segment 14 6344 434 6358 480 (by rfl) cert_652514

theorem cert_652736 : Represents 6136 762 :=
  segment 208 6136 762 6344 434 (by rfl) cert_652528

theorem cert_652760 : Represents 6112 5538 :=
  segment 24 6112 5538 6136 762 (by rfl) cert_652736

theorem cert_652848 : Represents 6024 5706 :=
  segment 88 6024 5706 6112 5538 (by rfl) cert_652760

theorem cert_652990 : Represents 5882 3182 :=
  segment 142 5882 3182 6024 5706 (by rfl) cert_652848

theorem cert_653022 : Represents 5850 5358 :=
  segment 32 5850 5358 5882 3182 (by rfl) cert_652990

theorem cert_653278 : Represents 5594 1454 :=
  segment 256 5594 1454 5850 5358 (by rfl) cert_653022

theorem cert_653452 : Represents 5420 5418 :=
  segment 174 5420 5418 5594 1454 (by rfl) cert_653278

theorem cert_653522 : Represents 5350 1472 :=
  segment 70 5350 1472 5420 5418 (by rfl) cert_653452

theorem cert_653616 : Represents 5256 1002 :=
  segment 94 5256 1002 5350 1472 (by rfl) cert_653522

theorem cert_653658 : Represents 5214 4192 :=
  segment 42 5214 4192 5256 1002 (by rfl) cert_653616

theorem cert_653712 : Represents 5160 138 :=
  segment 54 5160 138 5214 4192 (by rfl) cert_653658

theorem cert_653824 : Represents 5048 90 :=
  segment 112 5048 90 5160 138 (by rfl) cert_653712

theorem cert_653974 : Represents 4898 2758 :=
  segment 150 4898 2758 5048 90 (by rfl) cert_653824

theorem cert_654000 : Represents 4872 4056 :=
  segment 26 4872 4056 4898 2758 (by rfl) cert_653974

theorem cert_654006 : Represents 4866 3486 :=
  segment 6 4866 3486 4872 4056 (by rfl) cert_654000

theorem cert_654137 : Represents 4735 4733 :=
  segment 131 4735 4733 4866 3486 (by rfl) cert_654006

theorem cert_654154 : Represents 4736 4734 :=
  segment 16 4736 4734 4752 3736 (by rfl) cert_645844

theorem cert_654242 : Represents 4737 4735 :=
  segment 87 4737 4735 4824 0 (by rfl) (zero_represents 4824)

theorem cert_654255 : Represents 4738 4736 :=
  segment 12 4738 4736 4750 2616 (by rfl) cert_646199

theorem cert_654283 : Represents 4739 4737 :=
  segment 27 4739 4737 4766 4320 (by rfl) cert_639071

theorem cert_654304 : Represents 4740 4738 :=
  segment 20 4740 4738 4760 1512 (by rfl) cert_627001

theorem cert_654314 : Represents 4741 4739 :=
  segment 9 4741 4739 4750 2704 (by rfl) cert_636496

theorem cert_654517 : Represents 5172 5170 :=
  segment 202 5172 5170 5374 3864 (by rfl) cert_300331

theorem cert_654549 : Represents 5140 5138 :=
  segment 32 5140 5138 5172 5170 (by rfl) cert_654517

theorem cert_654601 : Represents 5088 2666 :=
  segment 52 5088 2666 5140 5138 (by rfl) cert_654549

theorem cert_654689 : Represents 5000 3210 :=
  segment 88 5000 3210 5088 2666 (by rfl) cert_654601

theorem cert_654945 : Represents 4744 4730 :=
  segment 256 4744 4730 5000 3210 (by rfl) cert_654689

theorem cert_654947 : Represents 4742 4740 :=
  segment 2 4742 4740 4744 4730 (by rfl) cert_654945

theorem cert_654965 : Represents 4743 4741 :=
  segment 17 4743 4741 4760 3496 (by rfl) cert_639306

theorem cert_655052 : Represents 4744 4742 :=
  segment 86 4744 4742 4830 296 (by rfl) cert_640827

theorem cert_655228 : Represents 4745 4743 :=
  segment 175 4745 4743 4920 3272 (by rfl) cert_614920

theorem cert_655349 : Represents 4746 4744 :=
  segment 120 4746 4744 4866 1662 (by rfl) cert_635812

theorem cert_655403 : Represents 4747 4745 :=
  segment 53 4747 4745 4800 3170 (by rfl) cert_174687

theorem cert_655464 : Represents 5062 4552 :=
  segment 60 5062 4552 5122 3326 (by rfl) cert_626378

theorem cert_655510 : Represents 5016 4890 :=
  segment 46 5016 4890 5062 4552 (by rfl) cert_655464

theorem cert_655592 : Represents 4934 1176 :=
  segment 82 4934 1176 5016 4890 (by rfl) cert_655510

theorem cert_655624 : Represents 4902 840 :=
  segment 32 4902 840 4934 1176 (by rfl) cert_655592

theorem cert_655778 : Represents 4748 4746 :=
  segment 154 4748 4746 4902 840 (by rfl) cert_655624

theorem cert_655806 : Represents 4749 4747 :=
  segment 27 4749 4747 4776 4216 (by rfl) cert_642204

theorem cert_655931 : Represents 4750 4748 :=
  segment 124 4750 4748 4874 3542 (by rfl) cert_358597

theorem cert_655956 : Represents 4864 264 :=
  segment 24 4864 264 4888 3752 (by rfl) cert_375638

theorem cert_656069 : Represents 4751 4749 :=
  segment 113 4751 4749 4864 264 (by rfl) cert_655956

theorem cert_656076 : Represents 4752 4750 :=
  segment 6 4752 4750 4758 4504 (by rfl) cert_646191

theorem cert_656333 : Represents 4938 1228 :=
  segment 256 4938 1228 5194 5046 (by rfl) cert_598506

theorem cert_656463 : Represents 4808 1426 :=
  segment 130 4808 1426 4938 1228 (by rfl) cert_656333

theorem cert_656518 : Represents 4753 4751 :=
  segment 55 4753 4751 4808 1426 (by rfl) cert_656463

theorem cert_656579 : Represents 4754 4752 :=
  segment 60 4754 4752 4814 4056 (by rfl) cert_634054

theorem cert_656617 : Represents 4755 4753 :=
  segment 37 4755 4753 4792 2824 (by rfl) cert_633660

theorem cert_656632 : Represents 4906 4790 :=
  segment 14 4906 4790 4920 2202 (by rfl) cert_375606

theorem cert_656782 : Represents 4756 4754 :=
  segment 150 4756 4754 4906 4790 (by rfl) cert_656632

theorem cert_656849 : Represents 4960 3554 :=
  segment 66 4960 3554 5026 358 (by rfl) cert_645570

theorem cert_656921 : Represents 4888 3328 :=
  segment 72 4888 3328 4960 3554 (by rfl) cert_656849

theorem cert_656947 : Represents 4862 3864 :=
  segment 26 4862 3864 4888 3328 (by rfl) cert_656921

theorem cert_657052 : Represents 4757 4755 :=
  segment 105 4757 4755 4862 3864 (by rfl) cert_656947

theorem cert_657063 : Represents 4758 4756 :=
  segment 10 4758 4756 4768 674 (by rfl) cert_646306

theorem cert_657142 : Represents 8802 422 :=
  segment 78 8802 422 8880 6312 (by rfl) cert_4495

theorem cert_657144 : Represents 8800 2306 :=
  segment 2 8800 2306 8802 422 (by rfl) cert_657142

theorem cert_657298 : Represents 8646 2048 :=
  segment 154 8646 2048 8800 2306 (by rfl) cert_657144

theorem cert_657304 : Represents 8640 32 :=
  segment 6 8640 32 8646 2048 (by rfl) cert_657298

theorem cert_657432 : Represents 8512 6432 :=
  segment 128 8512 6432 8640 32 (by rfl) cert_657304

theorem cert_657496 : Represents 8448 6072 :=
  segment 64 8448 6072 8512 6432 (by rfl) cert_657432

theorem cert_657712 : Represents 8232 7744 :=
  segment 216 8232 7744 8448 6072 (by rfl) cert_657496

theorem cert_657782 : Represents 8162 702 :=
  segment 70 8162 702 8232 7744 (by rfl) cert_657712

theorem cert_657810 : Represents 8134 6960 :=
  segment 28 8134 6960 8162 702 (by rfl) cert_657782

theorem cert_658038 : Represents 7906 3870 :=
  segment 228 7906 3870 8134 6960 (by rfl) cert_657810

theorem cert_658104 : Represents 7840 3232 :=
  segment 66 7840 3232 7906 3870 (by rfl) cert_658038

theorem cert_658160 : Represents 7784 18 :=
  segment 56 7784 18 7840 3232 (by rfl) cert_658104

theorem cert_658296 : Represents 7648 5320 :=
  segment 136 7648 5320 7784 18 (by rfl) cert_658160

theorem cert_658334 : Represents 7610 1454 :=
  segment 38 7610 1454 7648 5320 (by rfl) cert_658296

theorem cert_658434 : Represents 7510 4240 :=
  segment 100 7510 4240 7610 1454 (by rfl) cert_658334

theorem cert_658602 : Represents 7342 296 :=
  segment 168 7342 296 7510 4240 (by rfl) cert_658434

theorem cert_658710 : Represents 7234 4766 :=
  segment 108 7234 4766 7342 296 (by rfl) cert_658602

theorem cert_658738 : Represents 7206 368 :=
  segment 28 7206 368 7234 4766 (by rfl) cert_658710

theorem cert_658994 : Represents 6950 4280 :=
  segment 256 6950 4280 7206 368 (by rfl) cert_658738

theorem cert_659000 : Represents 6944 3106 :=
  segment 6 6944 3106 6950 4280 (by rfl) cert_658994

theorem cert_659030 : Represents 6914 5502 :=
  segment 30 6914 5502 6944 3106 (by rfl) cert_659000

theorem cert_659042 : Represents 6902 2808 :=
  segment 12 6902 2808 6914 5502 (by rfl) cert_659030

theorem cert_659050 : Represents 6894 6880 :=
  segment 8 6894 6880 6902 2808 (by rfl) cert_659042

theorem cert_659072 : Represents 6872 4456 :=
  segment 22 6872 4456 6894 6880 (by rfl) cert_659050

theorem cert_659162 : Represents 6782 1688 :=
  segment 90 6782 1688 6872 4456 (by rfl) cert_659072

theorem cert_659194 : Represents 6750 4328 :=
  segment 32 6750 4328 6782 1688 (by rfl) cert_659162

theorem cert_659368 : Represents 6576 4760 :=
  segment 174 6576 4760 6750 4328 (by rfl) cert_659194

theorem cert_659610 : Represents 6334 6072 :=
  segment 242 6334 6072 6576 4760 (by rfl) cert_659368

theorem cert_659688 : Represents 6256 5784 :=
  segment 78 6256 5784 6334 6072 (by rfl) cert_659610

theorem cert_659728 : Represents 6216 2898 :=
  segment 40 6216 2898 6256 5784 (by rfl) cert_659688

theorem cert_659922 : Represents 6022 3528 :=
  segment 194 6022 3528 6216 2898 (by rfl) cert_659728

theorem cert_660114 : Represents 5830 3144 :=
  segment 192 5830 3144 6022 3528 (by rfl) cert_659922

theorem cert_660142 : Represents 5802 822 :=
  segment 28 5802 822 5830 3144 (by rfl) cert_660114

theorem cert_660184 : Represents 5760 2 :=
  segment 42 5760 2 5802 822 (by rfl) cert_660142

theorem cert_660186 : Represents 5758 2880 :=
  segment 2 5758 2880 5760 2 (by rfl) cert_660184

theorem cert_660406 : Represents 5538 2910 :=
  segment 220 5538 2910 5758 2880 (by rfl) cert_660186

theorem cert_660440 : Represents 5504 128 :=
  segment 34 5504 128 5538 2910 (by rfl) cert_660406

theorem cert_660696 : Represents 5248 4936 :=
  segment 256 5248 4936 5504 128 (by rfl) cert_660440

theorem cert_660744 : Represents 5200 632 :=
  segment 48 5200 632 5248 4936 (by rfl) cert_660696

theorem cert_660832 : Represents 5112 3048 :=
  segment 88 5112 3048 5200 632 (by rfl) cert_660744

theorem cert_660924 : Represents 5020 5018 :=
  segment 92 5020 5018 5112 3048 (by rfl) cert_660832

theorem cert_661180 : Represents 4764 4638 :=
  segment 256 4764 4638 5020 5018 (by rfl) cert_660924

theorem cert_661185 : Represents 4759 4757 :=
  segment 5 4759 4757 4764 4638 (by rfl) cert_661180

theorem cert_661208 : Represents 4760 4758 :=
  segment 22 4760 4758 4782 336 (by rfl) cert_637534

theorem cert_661249 : Represents 4832 2432 :=
  segment 40 4832 2432 4872 458 (by rfl) cert_646918

theorem cert_661320 : Represents 4761 4759 :=
  segment 71 4761 4759 4832 2432 (by rfl) cert_661249

theorem cert_661355 : Represents 4910 3256 :=
  segment 34 4910 3256 4944 3480 (by rfl) cert_375582

theorem cert_661503 : Represents 4762 4760 :=
  segment 148 4762 4760 4910 3256 (by rfl) cert_661355

theorem cert_661760 : Represents 4770 4260 :=
  segment 256 4770 4260 5026 4446 (by rfl) cert_597471

theorem cert_661767 : Represents 4763 4761 :=
  segment 7 4763 4761 4770 4260 (by rfl) cert_661760

theorem cert_661868 : Represents 4765 4763 :=
  segment 99 4765 4763 4864 4330 (by rfl) cert_600566

theorem cert_661879 : Represents 4766 4764 :=
  segment 10 4766 4764 4776 682 (by rfl) cert_563298

theorem cert_661932 : Represents 4782 2736 :=
  segment 52 4782 2736 4834 1094 (by rfl) cert_529501

theorem cert_661947 : Represents 4767 4765 :=
  segment 15 4767 4765 4782 2736 (by rfl) cert_661932

theorem cert_662022 : Represents 4768 4766 :=
  segment 74 4768 4766 4842 2294 (by rfl) cert_597655

theorem cert_662062 : Represents 4769 4767 :=
  segment 39 4769 4767 4808 3506 (by rfl) cert_641557

theorem cert_662085 : Represents 4770 4768 :=
  segment 22 4770 4768 4792 1970 (by rfl) cert_636839

theorem cert_662125 : Represents 4771 4769 :=
  segment 39 4771 4769 4810 54 (by rfl) cert_648127

theorem cert_662128 : Represents 4772 4770 :=
  segment 2 4772 4770 4774 4760 (by rfl) cert_643652

theorem cert_662138 : Represents 4773 4771 :=
  segment 9 4773 4771 4782 2736 (by rfl) cert_661932

theorem cert_662185 : Represents 5800 4938 :=
  segment 46 5800 4938 5846 512 (by rfl) cert_625654

theorem cert_662283 : Represents 5702 3680 :=
  segment 98 5702 3680 5800 4938 (by rfl) cert_662185

theorem cert_662297 : Represents 5688 264 :=
  segment 14 5688 264 5702 3680 (by rfl) cert_662283

theorem cert_662383 : Represents 5602 5566 :=
  segment 86 5602 5566 5688 264 (by rfl) cert_662297

theorem cert_662447 : Represents 5538 4166 :=
  segment 64 5538 4166 5602 5566 (by rfl) cert_662383

theorem cert_662577 : Represents 5408 3168 :=
  segment 130 5408 3168 5538 4166 (by rfl) cert_662447

theorem cert_662585 : Represents 5400 2376 :=
  segment 8 5400 2376 5408 3168 (by rfl) cert_662577

theorem cert_662601 : Represents 5384 4042 :=
  segment 16 5384 4042 5400 2376 (by rfl) cert_662585

theorem cert_662703 : Represents 5282 350 :=
  segment 102 5282 350 5384 4042 (by rfl) cert_662601

theorem cert_662881 : Represents 5104 1402 :=
  segment 178 5104 1402 5282 350 (by rfl) cert_662703

theorem cert_662913 : Represents 5072 4250 :=
  segment 32 5072 4250 5104 1402 (by rfl) cert_662881

theorem cert_663089 : Represents 4896 4408 :=
  segment 176 4896 4408 5072 4250 (by rfl) cert_662913

theorem cert_663097 : Represents 4888 3226 :=
  segment 8 4888 3226 4896 4408 (by rfl) cert_663089

theorem cert_663161 : Represents 4824 1690 :=
  segment 64 4824 1690 4888 3226 (by rfl) cert_663097

theorem cert_663163 : Represents 4822 4040 :=
  segment 2 4822 4040 4824 1690 (by rfl) cert_663161

theorem cert_663211 : Represents 4774 4772 :=
  segment 48 4774 4772 4822 4040 (by rfl) cert_663163

theorem cert_663214 : Represents 5120 3010 :=
  segment 2 5120 3010 5122 1798 (by rfl) cert_647815

theorem cert_663258 : Represents 5076 5074 :=
  segment 44 5076 5074 5120 3010 (by rfl) cert_663214

theorem cert_663286 : Represents 5048 1906 :=
  segment 28 5048 1906 5076 5074 (by rfl) cert_663258

theorem cert_663390 : Represents 4944 4930 :=
  segment 104 4944 4930 5048 1906 (by rfl) cert_663286

theorem cert_663480 : Represents 4854 760 :=
  segment 90 4854 760 4944 4930 (by rfl) cert_663390

theorem cert_663559 : Represents 4775 4773 :=
  segment 79 4775 4773 4854 760 (by rfl) cert_663480

theorem cert_663576 : Represents 4776 4774 :=
  segment 16 4776 4774 4792 1184 (by rfl) cert_588076

theorem cert_663622 : Represents 4777 4775 :=
  segment 45 4777 4775 4822 4040 (by rfl) cert_663163

theorem cert_663717 : Represents 4778 4776 :=
  segment 94 4778 4776 4872 2520 (by rfl) cert_648393

theorem cert_663731 : Represents 4779 4777 :=
  segment 13 4779 4777 4792 768 (by rfl) cert_139188

theorem cert_663784 : Represents 4780 4778 :=
  segment 52 4780 4778 4832 2432 (by rfl) cert_661249

theorem cert_663818 : Represents 4781 4779 :=
  segment 33 4781 4779 4814 760 (by rfl) cert_630921

theorem cert_663863 : Represents 4782 4780 :=
  segment 44 4782 4780 4826 2318 (by rfl) cert_601201

theorem cert_663969 : Represents 4783 4781 :=
  segment 105 4783 4781 4888 82 (by rfl) cert_628737

theorem cert_663986 : Represents 4784 4782 :=
  segment 16 4784 4782 4800 1624 (by rfl) cert_646149

theorem cert_664004 : Represents 4785 4783 :=
  segment 17 4785 4783 4802 3358 (by rfl) cert_639264

theorem cert_664107 : Represents 4786 4784 :=
  segment 102 4786 4784 4888 1562 (by rfl) cert_649762

theorem cert_664228 : Represents 4944 3466 :=
  segment 120 4944 3466 5064 2776 (by rfl) cert_612157

theorem cert_664385 : Represents 4787 4785 :=
  segment 157 4787 4785 4944 3466 (by rfl) cert_664228

theorem cert_664408 : Represents 5736 3680 :=
  segment 22 5736 3680 5758 2880 (by rfl) cert_660186

theorem cert_664470 : Represents 5674 1494 :=
  segment 62 5674 1494 5736 3680 (by rfl) cert_664408

theorem cert_664642 : Represents 5502 5472 :=
  segment 172 5502 5472 5674 1494 (by rfl) cert_664470

theorem cert_664674 : Represents 5470 4448 :=
  segment 32 5470 4448 5502 5472 (by rfl) cert_664642

theorem cert_664680 : Represents 5464 5450 :=
  segment 6 5464 5450 5470 4448 (by rfl) cert_664674

theorem cert_664736 : Represents 5408 928 :=
  segment 56 5408 928 5464 5450 (by rfl) cert_664680

theorem cert_664896 : Represents 5248 314 :=
  segment 160 5248 314 5408 928 (by rfl) cert_664736

theorem cert_664944 : Represents 5200 4570 :=
  segment 48 5200 4570 5248 314 (by rfl) cert_664896

theorem cert_664966 : Represents 5178 3470 :=
  segment 22 5178 3470 5200 4570 (by rfl) cert_664944

theorem cert_664978 : Represents 5166 5136 :=
  segment 12 5166 5136 5178 3470 (by rfl) cert_664966

theorem cert_665066 : Represents 5078 1008 :=
  segment 88 5078 1008 5166 5136 (by rfl) cert_664978

theorem cert_665130 : Represents 5014 2368 :=
  segment 64 5014 2368 5078 1008 (by rfl) cert_665066

theorem cert_665182 : Represents 4962 4806 :=
  segment 52 4962 4806 5014 2368 (by rfl) cert_665130

theorem cert_665214 : Represents 4930 2654 :=
  segment 32 4930 2654 4962 4806 (by rfl) cert_665182

theorem cert_665356 : Represents 4788 4786 :=
  segment 142 4788 4786 4930 2654 (by rfl) cert_665214

theorem cert_665437 : Represents 6822 4032 :=
  segment 80 6822 4032 6902 2808 (by rfl) cert_659042

theorem cert_665665 : Represents 6594 6174 :=
  segment 228 6594 6174 6822 4032 (by rfl) cert_665437

theorem cert_665693 : Represents 6566 1904 :=
  segment 28 6566 1904 6594 6174 (by rfl) cert_665665

theorem cert_665699 : Represents 6560 1978 :=
  segment 6 6560 1978 6566 1904 (by rfl) cert_665693

theorem cert_665787 : Represents 6472 5770 :=
  segment 88 6472 5770 6560 1978 (by rfl) cert_665699

theorem cert_665817 : Represents 6442 3510 :=
  segment 30 6442 3510 6472 5770 (by rfl) cert_665787

theorem cert_665833 : Represents 6426 5998 :=
  segment 16 6426 5998 6442 3510 (by rfl) cert_665817

theorem cert_665901 : Represents 6358 5880 :=
  segment 68 6358 5880 6426 5998 (by rfl) cert_665833

theorem cert_665915 : Represents 6344 5912 :=
  segment 14 6344 5912 6358 5880 (by rfl) cert_665901

theorem cert_666043 : Represents 6216 4522 :=
  segment 128 6216 4522 6344 5912 (by rfl) cert_665915

theorem cert_666299 : Represents 5960 5400 :=
  segment 256 5960 5400 6216 4522 (by rfl) cert_666043

theorem cert_666315 : Represents 5944 5480 :=
  segment 16 5944 5480 5960 5400 (by rfl) cert_666299

theorem cert_666571 : Represents 5688 5480 :=
  segment 256 5688 5480 5944 5480 (by rfl) cert_666315

theorem cert_666613 : Represents 5646 5632 :=
  segment 42 5646 5632 5688 5480 (by rfl) cert_666571

theorem cert_666615 : Represents 5644 5642 :=
  segment 2 5644 5642 5646 5632 (by rfl) cert_666613

theorem cert_666627 : Represents 5632 5528 :=
  segment 12 5632 5528 5644 5642 (by rfl) cert_666615

theorem cert_666797 : Represents 5462 1904 :=
  segment 170 5462 1904 5632 5528 (by rfl) cert_666627

theorem cert_666909 : Represents 5350 3880 :=
  segment 112 5350 3880 5462 1904 (by rfl) cert_666797

theorem cert_667003 : Represents 5256 4256 :=
  segment 94 5256 4256 5350 3880 (by rfl) cert_666909

theorem cert_667099 : Represents 5160 5024 :=
  segment 96 5160 5024 5256 4256 (by rfl) cert_667003

theorem cert_667229 : Represents 5030 4776 :=
  segment 130 5030 4776 5160 5024 (by rfl) cert_667099

theorem cert_667267 : Represents 4992 2946 :=
  segment 38 4992 2946 5030 4776 (by rfl) cert_667229

theorem cert_667470 : Represents 4789 4787 :=
  segment 203 4789 4787 4992 2946 (by rfl) cert_667267

theorem cert_667679 : Represents 4992 1624 :=
  segment 208 4992 1624 5200 4570 (by rfl) cert_664944

theorem cert_667793 : Represents 4878 3128 :=
  segment 114 4878 3128 4992 1624 (by rfl) cert_667679

theorem cert_667881 : Represents 4790 4788 :=
  segment 88 4790 4788 4878 3128 (by rfl) cert_667793

theorem cert_667931 : Represents 4791 4789 :=
  segment 49 4791 4789 4840 4184 (by rfl) cert_619144

theorem cert_667940 : Represents 4792 4790 :=
  segment 8 4792 4790 4800 3778 (by rfl) cert_636446

theorem cert_667970 : Represents 4793 4791 :=
  segment 29 4793 4791 4822 3344 (by rfl) cert_629250

theorem cert_668107 : Represents 5026 2878 :=
  segment 136 5026 2878 5162 1206 (by rfl) cert_587706

theorem cert_668109 : Represents 5024 3232 :=
  segment 2 5024 3232 5026 2878 (by rfl) cert_668107

theorem cert_668141 : Represents 4992 1056 :=
  segment 32 4992 1056 5024 3232 (by rfl) cert_668109

theorem cert_668339 : Represents 4794 4792 :=
  segment 198 4794 4792 4992 1056 (by rfl) cert_668141

theorem cert_668375 : Represents 4795 4793 :=
  segment 35 4795 4793 4830 3168 (by rfl) cert_646765

theorem cert_668388 : Represents 4796 4794 :=
  segment 12 4796 4794 4808 2848 (by rfl) cert_642891

theorem cert_668400 : Represents 4797 4795 :=
  segment 11 4797 4795 4808 1426 (by rfl) cert_656463

theorem cert_668595 : Represents 4798 4796 :=
  segment 194 4798 4796 4992 1120 (by rfl) cert_587876

theorem cert_668597 : Represents 4799 4797 :=
  segment 1 4799 4797 4800 4794 (by rfl) cert_563274

theorem cert_668640 : Represents 4800 4798 :=
  segment 42 4800 4798 4842 4118 (by rfl) cert_646948

theorem cert_668750 : Represents 4801 4799 :=
  segment 109 4801 4799 4910 3192 (by rfl) cert_640398

theorem cert_669005 : Represents 4802 4800 :=
  segment 254 4802 4800 5056 896 (by rfl) cert_529279

theorem cert_669010 : Represents 5190 4552 :=
  segment 4 5190 4552 5194 150 (by rfl) cert_591569

theorem cert_669016 : Represents 5184 5176 :=
  segment 6 5184 5176 5190 4552 (by rfl) cert_669010

theorem cert_669208 : Represents 4992 4152 :=
  segment 192 4992 4152 5184 5176 (by rfl) cert_669016

theorem cert_669397 : Represents 4803 4801 :=
  segment 189 4803 4801 4992 4152 (by rfl) cert_669208

theorem cert_669408 : Represents 4804 4802 :=
  segment 10 4804 4802 4814 720 (by rfl) cert_635864

theorem cert_669535 : Represents 4824 2944 :=
  segment 126 4824 2944 4950 3248 (by rfl) cert_620495

theorem cert_669554 : Represents 4805 4803 :=
  segment 19 4805 4803 4824 2944 (by rfl) cert_669535

theorem cert_669573 : Represents 4806 4804 :=
  segment 18 4806 4804 4824 1690 (by rfl) cert_663161

theorem cert_669630 : Represents 4904 2368 :=
  segment 56 4904 2368 4960 800 (by rfl) cert_633908

theorem cert_669727 : Represents 4807 4805 :=
  segment 97 4807 4805 4904 2368 (by rfl) cert_669630

theorem cert_669744 : Represents 4808 4806 :=
  segment 16 4808 4806 4824 2944 (by rfl) cert_669535

theorem cert_669768 : Represents 4809 4807 :=
  segment 23 4809 4807 4832 2562 (by rfl) cert_584366

theorem cert_669903 : Represents 4810 4808 :=
  segment 134 4810 4808 4944 90 (by rfl) cert_622351

theorem cert_669930 : Represents 5000 4888 :=
  segment 26 5000 4888 5026 582 (by rfl) cert_587842

theorem cert_670034 : Represents 4896 832 :=
  segment 104 4896 832 5000 4888 (by rfl) cert_669930

theorem cert_670119 : Represents 4811 4809 :=
  segment 85 4811 4809 4896 832 (by rfl) cert_670034

theorem cert_670146 : Represents 4894 4832 :=
  segment 26 4894 4832 4920 4168 (by rfl) cert_646675

theorem cert_670168 : Represents 4872 2354 :=
  segment 22 4872 2354 4894 4832 (by rfl) cert_670146

theorem cert_670228 : Represents 4812 4810 :=
  segment 60 4812 4810 4872 2354 (by rfl) cert_670168

theorem cert_670357 : Represents 5032 5018 :=
  segment 128 5032 5018 5160 138 (by rfl) cert_653712

theorem cert_670429 : Represents 4960 1578 :=
  segment 72 4960 1578 5032 5018 (by rfl) cert_670357

theorem cert_670576 : Represents 4813 4811 :=
  segment 147 4813 4811 4960 1578 (by rfl) cert_670429

theorem cert_670625 : Represents 4814 4812 :=
  segment 48 4814 4812 4862 3864 (by rfl) cert_656947

theorem cert_670699 : Represents 4815 4813 :=
  segment 73 4815 4813 4888 3226 (by rfl) cert_663097

theorem cert_670956 : Represents 4904 56 :=
  segment 256 4904 56 5160 5024 (by rfl) cert_667099

theorem cert_671044 : Represents 4816 4814 :=
  segment 88 4816 4814 4904 56 (by rfl) cert_670956

theorem cert_671124 : Represents 4817 4815 :=
  segment 79 4817 4815 4896 3962 (by rfl) cert_563178

theorem cert_671129 : Represents 4818 4816 :=
  segment 4 4818 4816 4822 4760 (by rfl) cert_291965

theorem cert_671183 : Represents 4819 4817 :=
  segment 53 4819 4817 4872 1880 (by rfl) cert_601155

theorem cert_671230 : Represents 4938 4278 :=
  segment 46 4938 4278 4984 1256 (by rfl) cert_121988

theorem cert_671240 : Represents 4928 4674 :=
  segment 10 4928 4674 4938 4278 (by rfl) cert_671230

theorem cert_671348 : Represents 4820 4818 :=
  segment 108 4820 4818 4928 4674 (by rfl) cert_671240

theorem cert_671392 : Represents 4821 4819 :=
  segment 43 4821 4819 4864 264 (by rfl) cert_655956

theorem cert_671395 : Represents 4822 4820 :=
  segment 2 4822 4820 4824 4810 (by rfl) cert_623042

theorem cert_671410 : Represents 4906 118 :=
  segment 14 4906 118 4920 2720 (by rfl) cert_529415

theorem cert_671493 : Represents 4823 4821 :=
  segment 83 4823 4821 4906 118 (by rfl) cert_671410

theorem cert_671534 : Represents 5024 2304 :=
  segment 40 5024 2304 5064 2290 (by rfl) cert_606928

theorem cert_671614 : Represents 4944 1480 :=
  segment 80 4944 1480 5024 2304 (by rfl) cert_671534

theorem cert_671734 : Represents 4824 4822 :=
  segment 120 4824 4822 4944 1480 (by rfl) cert_671614

theorem cert_671798 : Represents 4825 4823 :=
  segment 63 4825 4823 4888 474 (by rfl) cert_646707

theorem cert_671827 : Represents 4860 4858 :=
  segment 28 4860 4858 4888 3328 (by rfl) cert_656921

theorem cert_671861 : Represents 4826 4824 :=
  segment 34 4826 4824 4860 4858 (by rfl) cert_671827

theorem cert_671984 : Represents 4904 882 :=
  segment 122 4904 882 5026 4670 (by rfl) cert_649624

theorem cert_672061 : Represents 4827 4825 :=
  segment 77 4827 4825 4904 882 (by rfl) cert_671984

theorem cert_672284 : Represents 4828 4826 :=
  segment 222 4828 4826 5050 4270 (by rfl) cert_597447

theorem cert_672352 : Represents 4829 4827 :=
  segment 67 4829 4827 4896 4408 (by rfl) cert_663089

theorem cert_672361 : Represents 4830 4828 :=
  segment 8 4830 4828 4838 3816 (by rfl) cert_149188

theorem cert_672403 : Represents 4831 4829 :=
  segment 41 4831 4829 4872 2354 (by rfl) cert_670168

theorem cert_672444 : Represents 4920 3738 :=
  segment 40 4920 3738 4960 3554 (by rfl) cert_656849

theorem cert_672532 : Represents 4832 4830 :=
  segment 88 4832 4830 4920 3738 (by rfl) cert_672444

theorem cert_672606 : Represents 4833 4831 :=
  segment 73 4833 4831 4906 118 (by rfl) cert_671410

theorem cert_672619 : Represents 4834 4832 :=
  segment 12 4834 4832 4846 3000 (by rfl) cert_607146

theorem cert_672651 : Represents 4835 4833 :=
  segment 31 4835 4833 4866 3486 (by rfl) cert_654006

theorem cert_672718 : Represents 4836 4834 :=
  segment 66 4836 4834 4902 2280 (by rfl) cert_614938

theorem cert_672775 : Represents 5000 856 :=
  segment 56 5000 856 5056 4162 (by rfl) cert_375470

theorem cert_672849 : Represents 4926 3296 :=
  segment 74 4926 3296 5000 856 (by rfl) cert_672775

theorem cert_672938 : Represents 4837 4835 :=
  segment 89 4837 4835 4926 3296 (by rfl) cert_672849

theorem cert_673021 : Represents 4838 4836 :=
  segment 82 4838 4836 4920 2074 (by rfl) cert_587948

theorem cert_673037 : Represents 4839 4837 :=
  segment 15 4839 4837 4854 4752 (by rfl) cert_637000

theorem cert_673054 : Represents 4840 4838 :=
  segment 16 4840 4838 4856 4704 (by rfl) cert_600574

theorem cert_673080 : Represents 4841 4839 :=
  segment 25 4841 4839 4866 2302 (by rfl) cert_619118

theorem cert_673105 : Represents 5032 952 :=
  segment 24 5032 952 5056 4568 (by rfl) cert_587812

theorem cert_673163 : Represents 4974 736 :=
  segment 58 4974 736 5032 952 (by rfl) cert_673105

theorem cert_673295 : Represents 4842 4840 :=
  segment 132 4842 4840 4974 736 (by rfl) cert_673163

theorem cert_673375 : Represents 4843 4841 :=
  segment 79 4843 4841 4922 1454 (by rfl) cert_569117

theorem cert_673386 : Represents 4844 4842 :=
  segment 10 4844 4842 4854 760 (by rfl) cert_663480

theorem cert_673411 : Represents 5890 2054 :=
  segment 24 5890 2054 5914 2382 (by rfl) cert_299791

theorem cert_673429 : Represents 5872 2266 :=
  segment 18 5872 2266 5890 2054 (by rfl) cert_673411

theorem cert_673455 : Represents 5846 5336 :=
  segment 26 5846 5336 5872 2266 (by rfl) cert_673429

theorem cert_673599 : Represents 5702 2024 :=
  segment 144 5702 2024 5846 5336 (by rfl) cert_673455

theorem cert_673613 : Represents 5688 5426 :=
  segment 14 5688 5426 5702 2024 (by rfl) cert_673599

theorem cert_673699 : Represents 5602 38 :=
  segment 86 5602 38 5688 5426 (by rfl) cert_673613

theorem cert_673763 : Represents 5538 1374 :=
  segment 64 5538 1374 5602 38 (by rfl) cert_673699

theorem cert_673901 : Represents 5400 3026 :=
  segment 138 5400 3026 5538 1374 (by rfl) cert_673763

theorem cert_673917 : Represents 5384 1344 :=
  segment 16 5384 1344 5400 3026 (by rfl) cert_673901

theorem cert_673957 : Represents 5344 2944 :=
  segment 40 5344 2944 5384 1344 (by rfl) cert_673917

theorem cert_674019 : Represents 5282 4934 :=
  segment 62 5282 4934 5344 2944 (by rfl) cert_673957

theorem cert_674115 : Represents 5186 4062 :=
  segment 96 5186 4062 5282 4934 (by rfl) cert_674019

theorem cert_674147 : Represents 5154 1470 :=
  segment 32 5154 1470 5186 4062 (by rfl) cert_674115

theorem cert_674317 : Represents 4984 186 :=
  segment 170 4984 186 5154 1470 (by rfl) cert_674147

theorem cert_674456 : Represents 4845 4843 :=
  segment 139 4845 4843 4984 186 (by rfl) cert_674317

theorem cert_674507 : Represents 4846 4844 :=
  segment 50 4846 4844 4896 832 (by rfl) cert_670034

theorem cert_674526 : Represents 4886 4856 :=
  segment 18 4886 4856 4904 882 (by rfl) cert_671984

theorem cert_674565 : Represents 4847 4845 :=
  segment 39 4847 4845 4886 4856 (by rfl) cert_674526

theorem cert_674616 : Represents 4848 4846 :=
  segment 50 4848 4846 4898 2758 (by rfl) cert_653974

theorem cert_674640 : Represents 4849 4847 :=
  segment 23 4849 4847 4872 4056 (by rfl) cert_654000

theorem cert_674809 : Represents 4920 4858 :=
  segment 168 4920 4858 5088 2848 (by rfl) cert_291699

theorem cert_674879 : Represents 4850 4848 :=
  segment 70 4850 4848 4920 4858 (by rfl) cert_674809

theorem cert_674935 : Represents 4851 4849 :=
  segment 55 4851 4849 4906 4790 (by rfl) cert_656632

theorem cert_675028 : Represents 4852 4850 :=
  segment 92 4852 4850 4944 1466 (by rfl) cert_529391

theorem cert_675040 : Represents 4853 4851 :=
  segment 11 4853 4851 4864 1538 (by rfl) cert_649403

theorem cert_675111 : Represents 5178 1166 :=
  segment 70 5178 1166 5248 602 (by rfl) cert_571837

theorem cert_675123 : Represents 5166 856 :=
  segment 12 5166 856 5178 1166 (by rfl) cert_675111

theorem cert_675143 : Represents 5146 718 :=
  segment 20 5146 718 5166 856 (by rfl) cert_675123

theorem cert_675145 : Represents 5144 2752 :=
  segment 2 5144 2752 5146 718 (by rfl) cert_675143

theorem cert_675171 : Represents 5118 2560 :=
  segment 26 5118 2560 5144 2752 (by rfl) cert_675145

theorem cert_675297 : Represents 4992 3768 :=
  segment 126 4992 3768 5118 2560 (by rfl) cert_675171

theorem cert_675379 : Represents 4910 1376 :=
  segment 82 4910 1376 4992 3768 (by rfl) cert_675297

theorem cert_675435 : Represents 4854 4852 :=
  segment 56 4854 4852 4910 1376 (by rfl) cert_675379

theorem cert_675509 : Represents 4855 4853 :=
  segment 73 4855 4853 4928 3648 (by rfl) cert_358543

theorem cert_675588 : Represents 4856 4854 :=
  segment 78 4856 4854 4934 1176 (by rfl) cert_655592

theorem cert_675658 : Represents 4857 4855 :=
  segment 69 4857 4855 4926 3296 (by rfl) cert_672849

theorem cert_675665 : Represents 4858 4856 :=
  segment 6 4858 4856 4864 4610 (by rfl) cert_643115

theorem cert_675671 : Represents 4859 4857 :=
  segment 5 4859 4857 4864 4738 (by rfl) cert_636767

theorem cert_675690 : Represents 4861 4859 :=
  segment 17 4861 4859 4878 1968 (by rfl) cert_633120

theorem cert_675803 : Represents 4862 4860 :=
  segment 112 4862 4860 4974 736 (by rfl) cert_673163

theorem cert_675854 : Represents 5430 5416 :=
  segment 50 5430 5416 5480 5106 (by rfl) cert_217504

theorem cert_675926 : Represents 5358 904 :=
  segment 72 5358 904 5430 5416 (by rfl) cert_675854

theorem cert_675990 : Represents 5294 1208 :=
  segment 64 5294 1208 5358 904 (by rfl) cert_675926

theorem cert_676004 : Represents 5280 4184 :=
  segment 14 5280 4184 5294 1208 (by rfl) cert_675990

theorem cert_676012 : Represents 5272 4466 :=
  segment 8 5272 4466 5280 4184 (by rfl) cert_676004

theorem cert_676028 : Represents 5256 2808 :=
  segment 16 5256 2808 5272 4466 (by rfl) cert_676012

theorem cert_676034 : Represents 5250 126 :=
  segment 6 5250 126 5256 2808 (by rfl) cert_676028

theorem cert_676110 : Represents 5174 5032 :=
  segment 76 5174 5032 5250 126 (by rfl) cert_676034

theorem cert_676202 : Represents 5082 2222 :=
  segment 92 5082 2222 5174 5032 (by rfl) cert_676110

theorem cert_676290 : Represents 4994 2182 :=
  segment 88 4994 2182 5082 2222 (by rfl) cert_676202

theorem cert_676421 : Represents 4863 4861 :=
  segment 131 4863 4861 4994 2182 (by rfl) cert_676290

theorem cert_676428 : Represents 5250 5126 :=
  segment 6 5250 5126 5256 2450 (by rfl) cert_138724

theorem cert_676480 : Represents 5198 2088 :=
  segment 52 5198 2088 5250 5126 (by rfl) cert_676428

theorem cert_676678 : Represents 5000 2776 :=
  segment 198 5000 2776 5198 2088 (by rfl) cert_676480

theorem cert_676814 : Represents 4864 4862 :=
  segment 136 4864 4862 5000 2776 (by rfl) cert_676678

theorem cert_676822 : Represents 4865 4863 :=
  segment 7 4865 4863 4872 4362 (by rfl) cert_641493

theorem cert_676835 : Represents 4866 4864 :=
  segment 12 4866 4864 4878 3128 (by rfl) cert_667793

theorem cert_676859 : Represents 4867 4865 :=
  segment 23 4867 4865 4890 1326 (by rfl) cert_646900

theorem cert_676948 : Represents 5000 4984 :=
  segment 88 5000 4984 5088 2424 (by rfl) cert_642611

theorem cert_677080 : Represents 4868 4866 :=
  segment 132 4868 4866 5000 4984 (by rfl) cert_676948

theorem cert_677100 : Represents 4869 4867 :=
  segment 19 4869 4867 4888 1554 (by rfl) cert_646902

theorem cert_677223 : Represents 4870 4868 :=
  segment 122 4870 4868 4992 4576 (by rfl) cert_8383

theorem cert_677234 : Represents 4952 4210 :=
  segment 10 4952 4210 4962 1310 (by rfl) cert_574399

theorem cert_677242 : Represents 4944 3320 :=
  segment 8 4944 3320 4952 4210 (by rfl) cert_677234

theorem cert_677315 : Represents 4871 4869 :=
  segment 73 4871 4869 4944 3320 (by rfl) cert_677242

theorem cert_677322 : Represents 4872 4870 :=
  segment 6 4872 4870 4878 4624 (by rfl) cert_300827

theorem cert_677345 : Represents 5178 1710 :=
  segment 22 5178 1710 5200 632 (by rfl) cert_660744

theorem cert_677347 : Represents 5176 1722 :=
  segment 2 5176 1722 5178 1710 (by rfl) cert_677345

theorem cert_677523 : Represents 5000 4434 :=
  segment 176 5000 4434 5176 1722 (by rfl) cert_677347

theorem cert_677613 : Represents 4910 4784 :=
  segment 90 4910 4784 5000 4434 (by rfl) cert_677523

theorem cert_677650 : Represents 4873 4871 :=
  segment 37 4873 4871 4910 4784 (by rfl) cert_677613

theorem cert_677907 : Represents 4874 4872 :=
  segment 256 4874 4872 5130 3350 (by rfl) cert_606862

theorem cert_677935 : Represents 4875 4873 :=
  segment 27 4875 4873 4902 840 (by rfl) cert_655624

theorem cert_677966 : Represents 5122 5120 :=
  segment 30 5122 5120 5152 930 (by rfl) cert_642547

theorem cert_678212 : Represents 4876 4874 :=
  segment 246 4876 4874 5122 5120 (by rfl) cert_677966

theorem cert_678266 : Represents 4877 4875 :=
  segment 53 4877 4875 4930 4382 (by rfl) cert_334751

theorem cert_678275 : Represents 4878 4876 :=
  segment 8 4878 4876 4886 3864 (by rfl) cert_218098

theorem cert_678301 : Represents 4879 4877 :=
  segment 25 4879 4877 4904 2368 (by rfl) cert_669630

theorem cert_678360 : Represents 4880 4878 :=
  segment 58 4880 4878 4938 4278 (by rfl) cert_671230

theorem cert_678369 : Represents 4952 3762 :=
  segment 8 4952 3762 4960 2114 (by rfl) cert_647977

theorem cert_678440 : Represents 4881 4879 :=
  segment 71 4881 4879 4952 3762 (by rfl) cert_678369

theorem cert_678519 : Represents 4882 4880 :=
  segment 78 4882 4880 4960 1578 (by rfl) cert_670429

theorem cert_678523 : Represents 4883 4881 :=
  segment 3 4883 4881 4886 4856 (by rfl) cert_674526

theorem cert_678532 : Represents 5048 3890 :=
  segment 8 5048 3890 5056 1096 (by rfl) cert_606936

theorem cert_678696 : Represents 4884 4882 :=
  segment 164 4884 4882 5048 3890 (by rfl) cert_678532

theorem cert_678764 : Represents 4885 4883 :=
  segment 67 4885 4883 4952 2112 (by rfl) cert_600478

theorem cert_678823 : Represents 4886 4884 :=
  segment 58 4886 4884 4944 1480 (by rfl) cert_671614

theorem cert_678864 : Represents 5048 3840 :=
  segment 40 5048 3840 5088 2666 (by rfl) cert_654601

theorem cert_679025 : Represents 4887 4885 :=
  segment 161 4887 4885 5048 3840 (by rfl) cert_678864

theorem cert_679082 : Represents 4888 4886 :=
  segment 56 4888 4886 4944 3320 (by rfl) cert_677242

theorem cert_679104 : Represents 4889 4887 :=
  segment 21 4889 4887 4910 1376 (by rfl) cert_675379

theorem cert_679109 : Represents 4890 4888 :=
  segment 4 4890 4888 4894 4832 (by rfl) cert_670146

theorem cert_679129 : Represents 4891 4889 :=
  segment 19 4891 4889 4910 1200 (by rfl) cert_300795

theorem cert_679166 : Represents 4892 4890 :=
  segment 36 4892 4890 4928 610 (by rfl) cert_630807

theorem cert_679218 : Represents 4893 4891 :=
  segment 51 4893 4891 4944 4856 (by rfl) cert_614896

theorem cert_679309 : Represents 4894 4892 :=
  segment 90 4894 4892 4984 186 (by rfl) cert_674317

theorem cert_679317 : Represents 4895 4893 :=
  segment 7 4895 4893 4902 4392 (by rfl) cert_649164

theorem cert_679472 : Represents 4896 4894 :=
  segment 154 4896 4894 5050 1486 (by rfl) cert_375476

theorem cert_679502 : Represents 4897 4895 :=
  segment 29 4897 4895 4926 3168 (by rfl) cert_8449

theorem cert_679515 : Represents 4898 4896 :=
  segment 12 4898 4896 4910 3256 (by rfl) cert_661355

theorem cert_679537 : Represents 4899 4897 :=
  segment 21 4899 4897 4920 3738 (by rfl) cert_672444

theorem cert_679548 : Represents 4900 4898 :=
  segment 10 4900 4898 4910 816 (by rfl) cert_648027

theorem cert_679592 : Represents 4901 4899 :=
  segment 43 4901 4899 4944 3466 (by rfl) cert_664228

theorem cert_679619 : Represents 5192 4914 :=
  segment 26 5192 4914 5218 2118 (by rfl) cert_529117

theorem cert_679635 : Represents 5176 4466 :=
  segment 16 5176 4466 5192 4914 (by rfl) cert_679619

theorem cert_679765 : Represents 5046 4696 :=
  segment 130 5046 4696 5176 4466 (by rfl) cert_679635

theorem cert_679795 : Represents 5016 4296 :=
  segment 30 5016 4296 5046 4696 (by rfl) cert_679765

theorem cert_679909 : Represents 4902 4900 :=
  segment 114 4902 4900 5016 4296 (by rfl) cert_679795

theorem cert_680095 : Represents 4903 4901 :=
  segment 185 4903 4901 5088 32 (by rfl) cert_593703

theorem cert_680144 : Represents 4904 4902 :=
  segment 48 4904 4902 4952 4136 (by rfl) cert_549406

theorem cert_680150 : Represents 4905 4903 :=
  segment 5 4905 4903 4910 4784 (by rfl) cert_677613

theorem cert_680207 : Represents 4906 4904 :=
  segment 56 4906 4904 4962 4806 (by rfl) cert_665182

theorem cert_680259 : Represents 4907 4905 :=
  segment 51 4907 4905 4958 592 (by rfl) cert_601069

theorem cert_680316 : Represents 4936 3296 :=
  segment 56 4936 3296 4992 4152 (by rfl) cert_669208

theorem cert_680344 : Represents 4908 4906 :=
  segment 28 4908 4906 4936 3296 (by rfl) cert_680316

theorem cert_680346 : Represents 4909 4907 :=
  segment 1 4909 4907 4910 4904 (by rfl) cert_622385

theorem cert_680395 : Represents 4910 4908 :=
  segment 48 4910 4908 4958 3440 (by rfl) cert_8417

theorem cert_680423 : Represents 4911 4909 :=
  segment 27 4911 4909 4938 3510 (by rfl) cert_569101

theorem cert_680432 : Represents 4992 3456 :=
  segment 8 4992 3456 5000 856 (by rfl) cert_672775

theorem cert_680512 : Represents 4912 4910 :=
  segment 80 4912 4910 4992 3456 (by rfl) cert_680432

theorem cert_680530 : Represents 4913 4911 :=
  segment 17 4913 4911 4930 2654 (by rfl) cert_665214

theorem cert_680569 : Represents 4914 4912 :=
  segment 38 4914 4912 4952 1402 (by rfl) cert_563122

theorem cert_680600 : Represents 5024 1600 :=
  segment 30 5024 1600 5054 0 (by rfl) (zero_represents 5054)

theorem cert_680709 : Represents 4915 4913 :=
  segment 109 4915 4913 5024 1600 (by rfl) cert_680600

theorem cert_680714 : Represents 4916 4914 :=
  segment 4 4916 4914 4920 4858 (by rfl) cert_674809

theorem cert_680790 : Represents 4917 4915 :=
  segment 75 4917 4915 4992 930 (by rfl) cert_334689

theorem cert_680799 : Represents 4918 4916 :=
  segment 8 4918 4916 4926 3904 (by rfl) cert_642773

theorem cert_680817 : Represents 4919 4917 :=
  segment 17 4919 4917 4936 3296 (by rfl) cert_680316

theorem cert_680844 : Represents 5422 3080 :=
  segment 26 5422 3080 5448 0 (by rfl) (zero_represents 5448)

theorem cert_680850 : Represents 5416 3434 :=
  segment 6 5416 3434 5422 3080 (by rfl) cert_680844

theorem cert_681106 : Represents 5160 4536 :=
  segment 256 5160 4536 5416 3434 (by rfl) cert_680850

theorem cert_681272 : Represents 4994 2430 :=
  segment 166 4994 2430 5160 4536 (by rfl) cert_681106

theorem cert_681306 : Represents 4960 506 :=
  segment 34 4960 506 4994 2430 (by rfl) cert_681272

theorem cert_681346 : Represents 4920 4918 :=
  segment 40 4920 4918 4960 506 (by rfl) cert_681306

theorem cert_681354 : Represents 4921 4919 :=
  segment 7 4921 4919 4928 4418 (by rfl) cert_569111

theorem cert_681361 : Represents 4922 4920 :=
  segment 6 4922 4920 4928 4674 (by rfl) cert_671240

theorem cert_681394 : Represents 4984 4922 :=
  segment 32 4984 4922 5016 4296 (by rfl) cert_679795

theorem cert_681455 : Represents 4923 4921 :=
  segment 61 4923 4921 4984 4922 (by rfl) cert_681394

theorem cert_681518 : Represents 4924 4922 :=
  segment 62 4924 4922 4986 78 (by rfl) cert_149040

theorem cert_681586 : Represents 4925 4923 :=
  segment 67 4925 4923 4992 3456 (by rfl) cert_680432

theorem cert_681613 : Represents 4926 4924 :=
  segment 26 4926 4924 4952 4210 (by rfl) cert_677234

theorem cert_681679 : Represents 4927 4925 :=
  segment 65 4927 4925 4992 3874 (by rfl) cert_597505

theorem cert_681714 : Represents 5510 3016 :=
  segment 34 5510 3016 5544 352 (by rfl) cert_291243

theorem cert_681770 : Represents 5454 2768 :=
  segment 56 5454 2768 5510 3016 (by rfl) cert_681714

theorem cert_681840 : Represents 5384 1944 :=
  segment 70 5384 1944 5454 2768 (by rfl) cert_681770

theorem cert_682050 : Represents 5174 1112 :=
  segment 210 5174 1112 5384 1944 (by rfl) cert_681840

theorem cert_682168 : Represents 5056 3434 :=
  segment 118 5056 3434 5174 1112 (by rfl) cert_682050

theorem cert_682296 : Represents 4928 4926 :=
  segment 128 4928 4926 5056 3434 (by rfl) cert_682168

theorem cert_682362 : Represents 4929 4927 :=
  segment 65 4929 4927 4994 2430 (by rfl) cert_681272

theorem cert_682385 : Represents 4930 4928 :=
  segment 22 4930 4928 4952 4576 (by rfl) cert_601075

theorem cert_682455 : Represents 4931 4929 :=
  segment 69 4931 4929 5000 3210 (by rfl) cert_654689

theorem cert_682458 : Represents 4932 4930 :=
  segment 2 4932 4930 4934 4920 (by rfl) cert_593857

theorem cert_682486 : Represents 4933 4931 :=
  segment 27 4933 4931 4960 1730 (by rfl) cert_645636

theorem cert_682569 : Represents 5048 872 :=
  segment 82 5048 872 5130 1782 (by rfl) cert_612091

theorem cert_682591 : Represents 5026 2502 :=
  segment 22 5026 2502 5048 872 (by rfl) cert_682569

theorem cert_682683 : Represents 4934 4932 :=
  segment 92 4934 4932 5026 2502 (by rfl) cert_682591

end Erdos261Finite
