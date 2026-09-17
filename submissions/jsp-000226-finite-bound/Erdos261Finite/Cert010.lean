import Erdos261Finite.Cert009

set_option maxRecDepth 4096
set_option maxHeartbeats 0
namespace Erdos261Finite

theorem cert_183593 : Represents 2720 1090 :=
  segment 2 2720 1090 2722 1638 (by rfl) cert_151304

theorem cert_183815 : Represents 2498 2078 :=
  segment 222 2498 2078 2720 1090 (by rfl) cert_183593

theorem cert_183947 : Represents 2366 208 :=
  segment 132 2366 208 2498 2078 (by rfl) cert_183815

theorem cert_184016 : Represents 2297 2295 :=
  segment 69 2297 2295 2366 208 (by rfl) cert_183947

theorem cert_184079 : Represents 2298 2296 :=
  segment 62 2298 2296 2360 2216 (by rfl) cert_141620

theorem cert_184163 : Represents 2299 2297 :=
  segment 83 2299 2297 2382 1624 (by rfl) cert_183467

theorem cert_184264 : Represents 2300 2298 :=
  segment 100 2300 2298 2400 1912 (by rfl) cert_180683

theorem cert_184285 : Represents 2434 1286 :=
  segment 20 2434 1286 2454 2288 (by rfl) cert_182157

theorem cert_184418 : Represents 2301 2299 :=
  segment 133 2301 2299 2434 1286 (by rfl) cert_184285

theorem cert_184433 : Represents 2880 776 :=
  segment 14 2880 776 2894 0 (by rfl) (zero_represents 2894)

theorem cert_184441 : Represents 2872 2394 :=
  segment 8 2872 2394 2880 776 (by rfl) cert_184433

theorem cert_184499 : Represents 2814 792 :=
  segment 58 2814 792 2872 2394 (by rfl) cert_184441

theorem cert_184567 : Represents 2746 1422 :=
  segment 68 2746 1422 2814 792 (by rfl) cert_184499

theorem cert_184569 : Represents 2744 1728 :=
  segment 2 2744 1728 2746 1422 (by rfl) cert_184567

theorem cert_184643 : Represents 2670 1072 :=
  segment 74 2670 1072 2744 1728 (by rfl) cert_184569

theorem cert_184655 : Represents 2658 2590 :=
  segment 12 2658 2590 2670 1072 (by rfl) cert_184643

theorem cert_184667 : Represents 2646 656 :=
  segment 12 2646 656 2658 2590 (by rfl) cert_184655

theorem cert_184689 : Represents 2624 2528 :=
  segment 22 2624 2528 2646 656 (by rfl) cert_184667

theorem cert_184691 : Represents 2622 1288 :=
  segment 2 2622 1288 2624 2528 (by rfl) cert_184689

theorem cert_184825 : Represents 2488 1760 :=
  segment 134 2488 1760 2622 1288 (by rfl) cert_184691

theorem cert_184915 : Represents 2398 352 :=
  segment 90 2398 352 2488 1760 (by rfl) cert_184825

theorem cert_185011 : Represents 2302 2300 :=
  segment 96 2302 2300 2398 352 (by rfl) cert_184915

theorem cert_185069 : Represents 2303 2301 :=
  segment 57 2303 2301 2360 1600 (by rfl) cert_40617

theorem cert_185080 : Represents 2304 2302 :=
  segment 10 2304 2302 2314 534 (by rfl) cert_136681

theorem cert_185087 : Represents 2530 198 :=
  segment 6 2530 198 2536 0 (by rfl) (zero_represents 2536)

theorem cert_185099 : Represents 2518 1632 :=
  segment 12 2518 1632 2530 198 (by rfl) cert_185087

theorem cert_185169 : Represents 2448 2434 :=
  segment 70 2448 2434 2518 1632 (by rfl) cert_185099

theorem cert_185312 : Represents 2305 2303 :=
  segment 143 2305 2303 2448 2434 (by rfl) cert_185169

theorem cert_185351 : Represents 2306 2304 :=
  segment 38 2306 2304 2344 1330 (by rfl) cert_182267

theorem cert_185383 : Represents 2307 2305 :=
  segment 31 2307 2305 2338 1374 (by rfl) cert_158837

theorem cert_185480 : Represents 2402 446 :=
  segment 96 2402 446 2498 1886 (by rfl) cert_172549

theorem cert_185574 : Represents 2308 2306 :=
  segment 94 2308 2306 2402 446 (by rfl) cert_185480

theorem cert_185604 : Represents 2309 2307 :=
  segment 29 2309 2307 2338 446 (by rfl) cert_156588

theorem cert_185685 : Represents 2350 1208 :=
  segment 80 2350 1208 2430 1416 (by rfl) cert_158745

theorem cert_185725 : Represents 2310 2308 :=
  segment 40 2310 2308 2350 1208 (by rfl) cert_185685

theorem cert_185741 : Represents 2311 2309 :=
  segment 15 2311 2309 2326 1264 (by rfl) cert_144090

theorem cert_185774 : Represents 2312 2310 :=
  segment 32 2312 2310 2344 1898 (by rfl) cert_160186

theorem cert_185823 : Represents 2350 1024 :=
  segment 48 2350 1024 2398 0 (by rfl) (zero_represents 2398)

theorem cert_185860 : Represents 2313 2311 :=
  segment 37 2313 2311 2350 1024 (by rfl) cert_185823

theorem cert_185873 : Represents 2518 888 :=
  segment 12 2518 888 2530 2334 (by rfl) cert_178274

theorem cert_185983 : Represents 2408 1056 :=
  segment 110 2408 1056 2518 888 (by rfl) cert_185873

theorem cert_186047 : Represents 2344 2290 :=
  segment 64 2344 2290 2408 1056 (by rfl) cert_185983

theorem cert_186077 : Represents 2314 2312 :=
  segment 30 2314 2312 2344 2290 (by rfl) cert_186047

theorem cert_186109 : Represents 2315 2313 :=
  segment 31 2315 2313 2346 1526 (by rfl) cert_163279

theorem cert_186136 : Represents 2366 2360 :=
  segment 26 2366 2360 2392 890 (by rfl) cert_10983

theorem cert_186164 : Represents 2338 2336 :=
  segment 28 2338 2336 2366 2360 (by rfl) cert_186136

theorem cert_186186 : Represents 2316 2314 :=
  segment 22 2316 2314 2338 2336 (by rfl) cert_186164

theorem cert_186283 : Represents 2434 390 :=
  segment 96 2434 390 2530 198 (by rfl) cert_185087

theorem cert_186285 : Represents 2432 706 :=
  segment 2 2432 706 2434 390 (by rfl) cert_186283

theorem cert_186365 : Represents 2352 2346 :=
  segment 80 2352 2346 2432 706 (by rfl) cert_186285

theorem cert_186400 : Represents 2317 2315 :=
  segment 35 2317 2315 2352 2346 (by rfl) cert_186365

theorem cert_186419 : Represents 2318 2316 :=
  segment 18 2318 2316 2336 1632 (by rfl) cert_142573

theorem cert_186427 : Represents 2319 2317 :=
  segment 7 2319 2317 2326 1816 (by rfl) cert_182686

theorem cert_186452 : Represents 2320 2318 :=
  segment 24 2320 2318 2344 960 (by rfl) cert_168320

theorem cert_186540 : Represents 2321 2319 :=
  segment 87 2321 2319 2408 970 (by rfl) cert_174167

theorem cert_186543 : Represents 2720 1632 :=
  segment 2 2720 1632 2722 1086 (by rfl) cert_148299

theorem cert_186575 : Represents 2688 2626 :=
  segment 32 2688 2626 2720 1632 (by rfl) cert_186543

theorem cert_186613 : Represents 2650 1902 :=
  segment 38 2650 1902 2688 2626 (by rfl) cert_186575

theorem cert_186737 : Represents 2526 2496 :=
  segment 124 2526 2496 2650 1902 (by rfl) cert_186613

theorem cert_186751 : Represents 2512 1834 :=
  segment 14 2512 1834 2526 2496 (by rfl) cert_186737

theorem cert_186759 : Represents 2504 1994 :=
  segment 8 2504 1994 2512 1834 (by rfl) cert_186751

theorem cert_186941 : Represents 2322 2320 :=
  segment 182 2322 2320 2504 1994 (by rfl) cert_186759

theorem cert_186950 : Represents 2424 2248 :=
  segment 8 2424 2248 2432 576 (by rfl) cert_133253

theorem cert_186982 : Represents 2392 552 :=
  segment 32 2392 552 2424 2248 (by rfl) cert_186950

theorem cert_187051 : Represents 2323 2321 :=
  segment 69 2323 2321 2392 552 (by rfl) cert_186982

theorem cert_187056 : Represents 2324 2322 :=
  segment 4 2324 2322 2328 2266 (by rfl) cert_165925

theorem cert_187058 : Represents 2325 2323 :=
  segment 1 2325 2323 2326 2320 (by rfl) cert_44623

theorem cert_187075 : Represents 2326 2324 :=
  segment 16 2326 2324 2342 1896 (by rfl) cert_154557

theorem cert_187181 : Represents 2327 2325 :=
  segment 105 2327 2325 2432 1858 (by rfl) cert_130112

theorem cert_187262 : Represents 2328 2326 :=
  segment 80 2328 2326 2408 1586 (by rfl) cert_183109

theorem cert_187278 : Represents 2329 2327 :=
  segment 15 2329 2327 2344 2290 (by rfl) cert_186047

theorem cert_187323 : Represents 2474 822 :=
  segment 44 2474 822 2518 1632 (by rfl) cert_185099

theorem cert_187341 : Represents 2456 2400 :=
  segment 18 2456 2400 2474 822 (by rfl) cert_187323

theorem cert_187467 : Represents 2330 2328 :=
  segment 126 2330 2328 2456 2400 (by rfl) cert_187341

theorem cert_187473 : Represents 2331 2329 :=
  segment 5 2331 2329 2336 2210 (by rfl) cert_182676

theorem cert_187492 : Represents 2332 2330 :=
  segment 18 2332 2330 2350 1024 (by rfl) cert_185823

theorem cert_187511 : Represents 2390 2216 :=
  segment 18 2390 2216 2408 1056 (by rfl) cert_185983

theorem cert_187568 : Represents 2333 2331 :=
  segment 57 2333 2331 2390 2216 (by rfl) cert_187511

theorem cert_187611 : Represents 2334 2332 :=
  segment 42 2334 2332 2376 2098 (by rfl) cert_180707

theorem cert_187621 : Represents 2335 2333 :=
  segment 9 2335 2333 2344 298 (by rfl) cert_146301

theorem cert_187632 : Represents 2336 2334 :=
  segment 10 2336 2334 2346 598 (by rfl) cert_169215

theorem cert_187698 : Represents 2337 2335 :=
  segment 65 2337 2335 2402 958 (by rfl) cert_22902

theorem cert_187711 : Represents 2339 2337 :=
  segment 11 2339 2337 2350 1208 (by rfl) cert_185685

theorem cert_187738 : Represents 2340 2338 :=
  segment 26 2340 2338 2366 208 (by rfl) cert_183947

theorem cert_187741 : Represents 3134 2456 :=
  segment 2 3134 2456 3136 418 (by rfl) cert_113169

theorem cert_187851 : Represents 3024 922 :=
  segment 110 3024 922 3134 2456 (by rfl) cert_187741

theorem cert_187965 : Represents 2910 248 :=
  segment 114 2910 248 3024 922 (by rfl) cert_187851

theorem cert_188067 : Represents 2808 2394 :=
  segment 102 2808 2394 2910 248 (by rfl) cert_187965

theorem cert_188089 : Represents 2786 1606 :=
  segment 22 2786 1606 2808 2394 (by rfl) cert_188067

theorem cert_188113 : Represents 2762 2582 :=
  segment 24 2762 2582 2786 1606 (by rfl) cert_188089

theorem cert_188133 : Represents 2742 888 :=
  segment 20 2742 888 2762 2582 (by rfl) cert_188113

theorem cert_188337 : Represents 2538 502 :=
  segment 204 2538 502 2742 888 (by rfl) cert_188133

theorem cert_188421 : Represents 2454 2328 :=
  segment 84 2454 2328 2538 502 (by rfl) cert_188337

theorem cert_188534 : Represents 2341 2339 :=
  segment 113 2341 2339 2454 2328 (by rfl) cert_188421

theorem cert_188539 : Represents 2658 806 :=
  segment 4 2658 806 2662 2256 (by rfl) cert_151364

theorem cert_188647 : Represents 2550 1864 :=
  segment 108 2550 1864 2658 806 (by rfl) cert_188539

theorem cert_188757 : Represents 2440 256 :=
  segment 110 2440 256 2550 1864 (by rfl) cert_188647

theorem cert_188855 : Represents 2342 2340 :=
  segment 98 2342 2340 2440 256 (by rfl) cert_188757

theorem cert_189031 : Represents 2343 2341 :=
  segment 175 2343 2341 2518 888 (by rfl) cert_185873

theorem cert_189046 : Represents 2344 2342 :=
  segment 14 2344 2342 2358 400 (by rfl) cert_40619

theorem cert_189068 : Represents 2345 2343 :=
  segment 21 2345 2343 2366 440 (by rfl) cert_171611

theorem cert_189113 : Represents 2346 2344 :=
  segment 44 2346 2344 2390 2216 (by rfl) cert_187511

theorem cert_189127 : Represents 2347 2345 :=
  segment 13 2347 2345 2360 242 (by rfl) cert_75728

theorem cert_189170 : Represents 2348 2346 :=
  segment 42 2348 2346 2390 656 (by rfl) cert_155900

theorem cert_189184 : Represents 2349 2347 :=
  segment 13 2349 2347 2362 270 (by rfl) cert_134211

theorem cert_189195 : Represents 2350 2348 :=
  segment 10 2350 2348 2360 626 (by rfl) cert_156566

theorem cert_189197 : Represents 2351 2349 :=
  segment 1 2351 2349 2352 2346 (by rfl) cert_186365

theorem cert_189248 : Represents 2352 2350 :=
  segment 50 2352 2350 2402 798 (by rfl) cert_181043

theorem cert_189303 : Represents 2466 1118 :=
  segment 54 2466 1118 2520 1640 (by rfl) cert_173245

theorem cert_189416 : Represents 2353 2351 :=
  segment 113 2353 2351 2466 1118 (by rfl) cert_189303

theorem cert_189457 : Represents 2354 2352 :=
  segment 40 2354 2352 2394 1646 (by rfl) cert_181336

theorem cert_189493 : Represents 2355 2353 :=
  segment 35 2355 2353 2390 1736 (by rfl) cert_75698

theorem cert_189514 : Represents 2357 2355 :=
  segment 19 2357 2355 2376 714 (by rfl) cert_173389

theorem cert_189533 : Represents 2358 2356 :=
  segment 18 2358 2356 2376 800 (by rfl) cert_178428

theorem cert_189541 : Represents 2359 2357 :=
  segment 7 2359 2357 2366 1856 (by rfl) cert_183298

theorem cert_189550 : Represents 2360 2358 :=
  segment 8 2360 2358 2368 1346 (by rfl) cert_44581

theorem cert_189582 : Represents 2361 2359 :=
  segment 31 2361 2359 2392 2280 (by rfl) cert_131179

theorem cert_189613 : Represents 2362 2360 :=
  segment 30 2362 2360 2392 552 (by rfl) cert_186982

theorem cert_189653 : Represents 2363 2361 :=
  segment 39 2363 2361 2402 1606 (by rfl) cert_170954

theorem cert_189658 : Represents 2364 2362 :=
  segment 4 2364 2362 2368 2306 (by rfl) cert_177119

theorem cert_189660 : Represents 2365 2363 :=
  segment 1 2365 2363 2366 2360 (by rfl) cert_186136

theorem cert_189675 : Represents 2410 2408 :=
  segment 14 2410 2408 2424 2248 (by rfl) cert_186950

theorem cert_189719 : Represents 2366 2364 :=
  segment 44 2366 2364 2410 2408 (by rfl) cert_189675

theorem cert_189807 : Represents 2367 2365 :=
  segment 87 2367 2365 2454 0 (by rfl) (zero_represents 2454)

theorem cert_189814 : Represents 2368 2366 :=
  segment 6 2368 2366 2374 2120 (by rfl) cert_183014

theorem cert_189870 : Represents 2369 2367 :=
  segment 55 2369 2367 2424 2042 (by rfl) cert_155866

theorem cert_189949 : Represents 2370 2368 :=
  segment 78 2370 2368 2448 776 (by rfl) cert_134125

theorem cert_189984 : Represents 2486 456 :=
  segment 34 2486 456 2520 698 (by rfl) cert_134053

theorem cert_190099 : Represents 2371 2369 :=
  segment 115 2371 2369 2486 456 (by rfl) cert_189984

theorem cert_190166 : Represents 2462 2440 :=
  segment 66 2462 2440 2528 2434 (by rfl) cert_143888

theorem cert_190256 : Represents 2372 2370 :=
  segment 90 2372 2370 2462 2440 (by rfl) cert_190166

theorem cert_190286 : Represents 2373 2371 :=
  segment 29 2373 2371 2402 446 (by rfl) cert_185480

theorem cert_190403 : Represents 2374 2372 :=
  segment 116 2374 2372 2490 1966 (by rfl) cert_151536

theorem cert_190431 : Represents 2375 2373 :=
  segment 27 2375 2373 2402 1446 (by rfl) cert_20110

theorem cert_190490 : Represents 2376 2374 :=
  segment 58 2376 2374 2434 422 (by rfl) cert_134139

theorem cert_190570 : Represents 2377 2375 :=
  segment 79 2377 2375 2456 1234 (by rfl) cert_173309

theorem cert_190601 : Represents 2378 2376 :=
  segment 30 2378 2376 2408 2176 (by rfl) cert_151618

theorem cert_190613 : Represents 2379 2377 :=
  segment 11 2379 2377 2390 1368 (by rfl) cert_152494

theorem cert_190626 : Represents 2422 2392 :=
  segment 12 2422 2392 2434 134 (by rfl) cert_117058

theorem cert_190668 : Represents 2380 2378 :=
  segment 42 2380 2378 2422 2392 (by rfl) cert_190626

theorem cert_190778 : Represents 2381 2379 :=
  segment 109 2381 2379 2490 526 (by rfl) cert_148531

theorem cert_190781 : Represents 2382 2380 :=
  segment 2 2382 2380 2384 2370 (by rfl) cert_152500

theorem cert_190946 : Represents 2598 2232 :=
  segment 164 2598 2232 2762 2582 (by rfl) cert_188113

theorem cert_191100 : Represents 2444 2442 :=
  segment 154 2444 2442 2598 2232 (by rfl) cert_190946

theorem cert_191104 : Represents 2440 458 :=
  segment 4 2440 458 2444 2442 (by rfl) cert_191100

theorem cert_191161 : Represents 2383 2381 :=
  segment 57 2383 2381 2440 458 (by rfl) cert_191104

theorem cert_191274 : Represents 2384 2382 :=
  segment 112 2384 2382 2496 1984 (by rfl) cert_155794

theorem cert_191322 : Represents 2385 2383 :=
  segment 47 2385 2383 2432 706 (by rfl) cert_186285

theorem cert_191393 : Represents 2386 2384 :=
  segment 70 2386 2384 2456 1224 (by rfl) cert_172591

theorem cert_191471 : Represents 2387 2385 :=
  segment 77 2387 2385 2464 1568 (by rfl) cert_141516

theorem cert_191518 : Represents 2388 2386 :=
  segment 46 2388 2386 2434 2302 (by rfl) cert_120100

theorem cert_191528 : Represents 2389 2387 :=
  segment 9 2389 2387 2398 352 (by rfl) cert_184915

theorem cert_191539 : Represents 2390 2388 :=
  segment 10 2390 2388 2400 706 (by rfl) cert_144994

theorem cert_191583 : Represents 2391 2389 :=
  segment 43 2391 2389 2434 102 (by rfl) cert_177053

theorem cert_191658 : Represents 2392 2390 :=
  segment 74 2392 2390 2466 1118 (by rfl) cert_189303

theorem cert_191723 : Represents 2722 222 :=
  segment 64 2722 222 2786 1574 (by rfl) cert_113519

theorem cert_191965 : Represents 2480 1000 :=
  segment 242 2480 1000 2722 222 (by rfl) cert_191723

theorem cert_192052 : Represents 2393 2391 :=
  segment 87 2393 2391 2480 1000 (by rfl) cert_191965

theorem cert_192093 : Represents 2394 2392 :=
  segment 40 2394 2392 2434 2046 (by rfl) cert_178370

theorem cert_192174 : Represents 2470 2408 :=
  segment 80 2470 2408 2550 688 (by rfl) cert_156376

theorem cert_192210 : Represents 2434 2432 :=
  segment 36 2434 2432 2470 2408 (by rfl) cert_192174

theorem cert_192212 : Represents 2432 608 :=
  segment 2 2432 608 2434 2432 (by rfl) cert_192210

theorem cert_192249 : Represents 2395 2393 :=
  segment 37 2395 2393 2432 608 (by rfl) cert_192212

theorem cert_192288 : Represents 2396 2394 :=
  segment 38 2396 2394 2434 1286 (by rfl) cert_184285

theorem cert_192292 : Represents 2397 2395 :=
  segment 3 2397 2395 2400 2370 (by rfl) cert_181194

theorem cert_192301 : Represents 2398 2396 :=
  segment 8 2398 2396 2406 1384 (by rfl) cert_10969

theorem cert_192335 : Represents 2399 2397 :=
  segment 33 2399 2397 2432 608 (by rfl) cert_192212

theorem cert_192362 : Represents 2400 2398 :=
  segment 26 2400 2398 2426 206 (by rfl) cert_173027

theorem cert_192396 : Represents 2401 2399 :=
  segment 33 2401 2399 2434 1406 (by rfl) cert_172613

theorem cert_192411 : Represents 2402 2400 :=
  segment 14 2402 2400 2416 2024 (by rfl) cert_172631

theorem cert_192530 : Represents 2506 150 :=
  segment 118 2506 150 2624 2496 (by rfl) cert_119910

theorem cert_192633 : Represents 2403 2401 :=
  segment 103 2403 2401 2506 150 (by rfl) cert_192530

theorem cert_192638 : Represents 2430 2176 :=
  segment 4 2430 2176 2434 774 (by rfl) cert_158741

theorem cert_192664 : Represents 2404 2402 :=
  segment 26 2404 2402 2430 2176 (by rfl) cert_192638

theorem cert_192715 : Represents 2470 1864 :=
  segment 50 2470 1864 2520 882 (by rfl) cert_172527

theorem cert_192719 : Represents 2466 1350 :=
  segment 4 2466 1350 2470 1864 (by rfl) cert_192715

theorem cert_192780 : Represents 2405 2403 :=
  segment 61 2405 2403 2466 1350 (by rfl) cert_192719

theorem cert_192815 : Represents 2862 2856 :=
  segment 34 2862 2856 2896 1592 (by rfl) cert_129648

theorem cert_192871 : Represents 2806 1256 :=
  segment 56 2806 1256 2862 2856 (by rfl) cert_192815

theorem cert_192905 : Represents 2772 2770 :=
  segment 34 2772 2770 2806 1256 (by rfl) cert_192871

theorem cert_192955 : Represents 2722 1598 :=
  segment 50 2722 1598 2772 2770 (by rfl) cert_192905

theorem cert_193011 : Represents 2666 1526 :=
  segment 56 2666 1526 2722 1598 (by rfl) cert_192955

theorem cert_193101 : Represents 2576 264 :=
  segment 90 2576 264 2666 1526 (by rfl) cert_193011

theorem cert_193127 : Represents 2550 1376 :=
  segment 26 2550 1376 2576 264 (by rfl) cert_193101

theorem cert_193167 : Represents 2510 2320 :=
  segment 40 2510 2320 2550 1376 (by rfl) cert_193127

theorem cert_193229 : Represents 2448 1816 :=
  segment 62 2448 1816 2510 2320 (by rfl) cert_193167

theorem cert_193271 : Represents 2406 2404 :=
  segment 42 2406 2404 2448 1816 (by rfl) cert_193229

theorem cert_193313 : Represents 2407 2405 :=
  segment 41 2407 2405 2448 1816 (by rfl) cert_193229

theorem cert_193368 : Represents 2408 2406 :=
  segment 54 2408 2406 2462 2440 (by rfl) cert_190166

theorem cert_193409 : Represents 2592 2018 :=
  segment 40 2592 2018 2632 2354 (by rfl) cert_143784

theorem cert_193527 : Represents 2474 2006 :=
  segment 118 2474 2006 2592 2018 (by rfl) cert_193409

theorem cert_193592 : Represents 2409 2407 :=
  segment 65 2409 2407 2474 2006 (by rfl) cert_193527

theorem cert_193624 : Represents 2474 2472 :=
  segment 30 2474 2472 2504 2026 (by rfl) cert_160026

theorem cert_193687 : Represents 2411 2409 :=
  segment 63 2411 2409 2474 2472 (by rfl) cert_193624

theorem cert_193690 : Represents 2412 2410 :=
  segment 2 2412 2410 2414 2400 (by rfl) cert_120120

theorem cert_193764 : Represents 2413 2411 :=
  segment 73 2413 2411 2486 328 (by rfl) cert_113819

theorem cert_193785 : Represents 2414 2412 :=
  segment 20 2414 2412 2434 390 (by rfl) cert_186283

theorem cert_193916 : Represents 2494 2368 :=
  segment 130 2494 2368 2624 2528 (by rfl) cert_184689

theorem cert_193995 : Represents 2415 2413 :=
  segment 79 2415 2413 2494 2368 (by rfl) cert_193916

theorem cert_194032 : Represents 2430 2416 :=
  segment 36 2430 2416 2466 1982 (by rfl) cert_180617

theorem cert_194046 : Represents 2416 2414 :=
  segment 14 2416 2414 2430 2416 (by rfl) cert_194032

theorem cert_194094 : Represents 2417 2415 :=
  segment 47 2417 2415 2464 512 (by rfl) cert_170892

theorem cert_194181 : Represents 2418 2416 :=
  segment 86 2418 2416 2504 2432 (by rfl) cert_22800

theorem cert_194185 : Represents 2419 2417 :=
  segment 3 2419 2417 2422 2392 (by rfl) cert_190626

theorem cert_194258 : Represents 2824 672 :=
  segment 72 2824 672 2896 1306 (by rfl) cert_124076

theorem cert_194266 : Represents 2816 234 :=
  segment 8 2816 234 2824 672 (by rfl) cert_194258

theorem cert_194276 : Represents 2806 1552 :=
  segment 10 2806 1552 2816 234 (by rfl) cert_194266

theorem cert_194404 : Represents 2678 1992 :=
  segment 128 2678 1992 2806 1552 (by rfl) cert_194276

theorem cert_194466 : Represents 2616 2602 :=
  segment 62 2616 2602 2678 1992 (by rfl) cert_194404

theorem cert_194662 : Represents 2420 2418 :=
  segment 196 2420 2418 2616 2602 (by rfl) cert_194466

theorem cert_194706 : Represents 2421 2419 :=
  segment 43 2421 2419 2464 0 (by rfl) (zero_represents 2464)

theorem cert_194719 : Represents 2422 2420 :=
  segment 12 2422 2420 2434 646 (by rfl) cert_148587

theorem cert_194740 : Represents 2742 1856 :=
  segment 20 2742 1856 2762 182 (by rfl) cert_180321

theorem cert_194828 : Represents 2654 608 :=
  segment 88 2654 608 2742 1856 (by rfl) cert_194740

theorem cert_194944 : Represents 2538 2038 :=
  segment 116 2538 2038 2654 608 (by rfl) cert_194828

theorem cert_194978 : Represents 2504 1208 :=
  segment 34 2504 1208 2538 2038 (by rfl) cert_194944

theorem cert_195059 : Represents 2423 2421 :=
  segment 81 2423 2421 2504 1208 (by rfl) cert_194978

theorem cert_195066 : Represents 2424 2422 :=
  segment 6 2424 2422 2430 2176 (by rfl) cert_192638

theorem cert_195082 : Represents 2425 2423 :=
  segment 15 2425 2423 2440 458 (by rfl) cert_191104

theorem cert_195097 : Represents 2426 2424 :=
  segment 14 2426 2424 2440 256 (by rfl) cert_188757

theorem cert_195137 : Represents 2427 2425 :=
  segment 39 2427 2425 2466 1350 (by rfl) cert_192719

theorem cert_195140 : Represents 2428 2426 :=
  segment 2 2428 2426 2430 2416 (by rfl) cert_194032

theorem cert_195186 : Represents 2429 2427 :=
  segment 45 2429 2427 2474 822 (by rfl) cert_187323

theorem cert_195295 : Represents 2430 2428 :=
  segment 108 2430 2428 2538 502 (by rfl) cert_188337

theorem cert_195371 : Represents 2431 2429 :=
  segment 75 2431 2429 2506 150 (by rfl) cert_192530

theorem cert_195382 : Represents 2432 2430 :=
  segment 10 2432 2430 2442 790 (by rfl) cert_158733

theorem cert_195390 : Represents 2433 2431 :=
  segment 7 2433 2431 2440 1930 (by rfl) cert_40537

theorem cert_195421 : Represents 2435 2433 :=
  segment 29 2435 2433 2464 58 (by rfl) cert_182147

theorem cert_195458 : Represents 2436 2434 :=
  segment 36 2436 2434 2472 18 (by rfl) cert_75616

theorem cert_195492 : Represents 2437 2435 :=
  segment 33 2437 2435 2470 1864 (by rfl) cert_192715

theorem cert_195509 : Represents 2518 2424 :=
  segment 16 2518 2424 2534 80 (by rfl) cert_120000

theorem cert_195589 : Represents 2438 2436 :=
  segment 80 2438 2436 2518 2424 (by rfl) cert_195509

theorem cert_195607 : Represents 2439 2437 :=
  segment 17 2439 2437 2456 2400 (by rfl) cert_187341

theorem cert_195634 : Represents 2440 2438 :=
  segment 26 2440 2438 2466 702 (by rfl) cert_173299

theorem cert_195715 : Represents 3056 362 :=
  segment 80 3056 362 3136 2720 (by rfl) cert_179947

theorem cert_195787 : Represents 2984 2784 :=
  segment 72 2984 2784 3056 362 (by rfl) cert_195715

theorem cert_195933 : Represents 2838 2368 :=
  segment 146 2838 2368 2984 2784 (by rfl) cert_195787

theorem cert_195985 : Represents 2786 1214 :=
  segment 52 2786 1214 2838 2368 (by rfl) cert_195933

theorem cert_195989 : Represents 2782 1120 :=
  segment 4 2782 1120 2786 1214 (by rfl) cert_195985

theorem cert_196051 : Represents 2720 1986 :=
  segment 62 2720 1986 2782 1120 (by rfl) cert_195989

theorem cert_196153 : Represents 2618 14 :=
  segment 102 2618 14 2720 1986 (by rfl) cert_196051

theorem cert_196330 : Represents 2441 2439 :=
  segment 177 2441 2439 2618 14 (by rfl) cert_196153

theorem cert_196353 : Represents 2442 2440 :=
  segment 22 2442 2440 2464 1578 (by rfl) cert_40513

theorem cert_196442 : Represents 2562 1926 :=
  segment 88 2562 1926 2650 2478 (by rfl) cert_113655

theorem cert_196454 : Represents 2550 1992 :=
  segment 12 2550 1992 2562 1926 (by rfl) cert_196442

theorem cert_196561 : Represents 2443 2441 :=
  segment 107 2443 2441 2550 1992 (by rfl) cert_196454

theorem cert_196622 : Represents 2445 2443 :=
  segment 59 2445 2443 2504 1208 (by rfl) cert_194978

theorem cert_196625 : Represents 2446 2444 :=
  segment 2 2446 2444 2448 2434 (by rfl) cert_185169

theorem cert_196659 : Represents 2447 2445 :=
  segment 33 2447 2445 2480 1000 (by rfl) cert_191965

theorem cert_196702 : Represents 2448 2446 :=
  segment 42 2448 2446 2490 46 (by rfl) cert_176997

theorem cert_196708 : Represents 2449 2447 :=
  segment 5 2449 2447 2454 2328 (by rfl) cert_188421

theorem cert_196729 : Represents 2498 2398 :=
  segment 20 2498 2398 2518 2424 (by rfl) cert_195509

theorem cert_196777 : Represents 2450 2448 :=
  segment 48 2450 2448 2498 2398 (by rfl) cert_196729

theorem cert_196781 : Represents 2451 2449 :=
  segment 3 2451 2449 2454 2424 (by rfl) cert_173823

theorem cert_196864 : Represents 2590 1232 :=
  segment 82 2590 1232 2672 1658 (by rfl) cert_170684

theorem cert_196924 : Represents 2530 2342 :=
  segment 60 2530 2342 2590 1232 (by rfl) cert_196864

theorem cert_197002 : Represents 2452 2450 :=
  segment 78 2452 2450 2530 2342 (by rfl) cert_196924

theorem cert_197004 : Represents 2453 2451 :=
  segment 1 2453 2451 2454 2448 (by rfl) cert_133231

theorem cert_197053 : Represents 2454 2452 :=
  segment 48 2454 2452 2502 1000 (by rfl) cert_180581

theorem cert_197094 : Represents 2584 2144 :=
  segment 40 2584 2144 2624 130 (by rfl) cert_113681

theorem cert_197223 : Represents 2455 2453 :=
  segment 129 2455 2453 2584 2144 (by rfl) cert_197094

theorem cert_197280 : Represents 2456 2454 :=
  segment 56 2456 2454 2512 1834 (by rfl) cert_186751

theorem cert_197288 : Represents 2457 2455 :=
  segment 7 2457 2455 2464 1954 (by rfl) cert_180981

theorem cert_197305 : Represents 2458 2456 :=
  segment 16 2458 2456 2474 2006 (by rfl) cert_193527

theorem cert_197356 : Represents 2526 1664 :=
  segment 50 2526 1664 2576 264 (by rfl) cert_193101

theorem cert_197423 : Represents 2459 2457 :=
  segment 67 2459 2457 2526 1664 (by rfl) cert_197356

theorem cert_197456 : Represents 2496 2434 :=
  segment 32 2496 2434 2528 96 (by rfl) cert_124444

theorem cert_197492 : Represents 2460 2458 :=
  segment 36 2460 2458 2496 2434 (by rfl) cert_197456

theorem cert_197624 : Represents 2461 2459 :=
  segment 131 2461 2459 2592 416 (by rfl) cert_170764

theorem cert_197639 : Represents 2560 64 :=
  segment 14 2560 64 2574 1416 (by rfl) cert_148447

theorem cert_197665 : Represents 2534 952 :=
  segment 26 2534 952 2560 64 (by rfl) cert_197639

theorem cert_197737 : Represents 2462 2460 :=
  segment 72 2462 2460 2534 952 (by rfl) cert_197665

theorem cert_197746 : Represents 2558 512 :=
  segment 8 2558 512 2566 432 (by rfl) cert_124406

theorem cert_197841 : Represents 2463 2461 :=
  segment 95 2463 2461 2558 512 (by rfl) cert_197746

theorem cert_197898 : Represents 2464 2462 :=
  segment 56 2464 2462 2520 1824 (by rfl) cert_131051

theorem cert_197949 : Represents 2600 1386 :=
  segment 50 2600 1386 2650 174 (by rfl) cert_119884

theorem cert_198084 : Represents 2465 2463 :=
  segment 135 2465 2463 2600 1386 (by rfl) cert_197949

theorem cert_198089 : Represents 2466 2464 :=
  segment 4 2466 2464 2470 2408 (by rfl) cert_192174

theorem cert_198116 : Represents 2496 1866 :=
  segment 26 2496 1866 2522 1006 (by rfl) cert_172525

theorem cert_198145 : Represents 2467 2465 :=
  segment 29 2467 2465 2496 1866 (by rfl) cert_198116

theorem cert_198188 : Represents 2468 2466 :=
  segment 42 2468 2466 2510 2320 (by rfl) cert_193167

theorem cert_198216 : Represents 2469 2467 :=
  segment 27 2469 2467 2496 896 (by rfl) cert_170860

theorem cert_198359 : Represents 3072 416 :=
  segment 142 3072 416 3214 704 (by rfl) cert_179869

theorem cert_198399 : Represents 3032 160 :=
  segment 40 3032 160 3072 416 (by rfl) cert_198359

theorem cert_198541 : Represents 2890 1686 :=
  segment 142 2890 1686 3032 160 (by rfl) cert_198399

theorem cert_198615 : Represents 2816 288 :=
  segment 74 2816 288 2890 1686 (by rfl) cert_198541

theorem cert_198639 : Represents 2792 1976 :=
  segment 24 2792 1976 2816 288 (by rfl) cert_198615

theorem cert_198663 : Represents 2768 842 :=
  segment 24 2768 842 2792 1976 (by rfl) cert_198639

theorem cert_198799 : Represents 2632 1880 :=
  segment 136 2632 1880 2768 842 (by rfl) cert_198663

theorem cert_198805 : Represents 2626 358 :=
  segment 6 2626 358 2632 1880 (by rfl) cert_198799

theorem cert_198935 : Represents 2496 1626 :=
  segment 130 2496 1626 2626 358 (by rfl) cert_198805

theorem cert_198961 : Represents 2470 2468 :=
  segment 26 2470 2468 2496 1626 (by rfl) cert_198935

theorem cert_198977 : Represents 2471 2469 :=
  segment 15 2471 2469 2486 456 (by rfl) cert_189984

theorem cert_198994 : Represents 2502 1992 :=
  segment 16 2502 1992 2518 320 (by rfl) cert_148503

theorem cert_199024 : Represents 2472 2470 :=
  segment 30 2472 2470 2502 1992 (by rfl) cert_198994

theorem cert_199050 : Represents 2473 2471 :=
  segment 25 2473 2471 2498 2398 (by rfl) cert_196729

theorem cert_199127 : Represents 2475 2473 :=
  segment 75 2475 2473 2550 0 (by rfl) (zero_represents 2550)

theorem cert_199174 : Represents 2476 2474 :=
  segment 46 2476 2474 2522 1518 (by rfl) cert_173243

theorem cert_199186 : Represents 2477 2475 :=
  segment 11 2477 2475 2488 1760 (by rfl) cert_184825

theorem cert_199205 : Represents 2478 2476 :=
  segment 18 2478 2476 2496 1626 (by rfl) cert_198935

theorem cert_199242 : Represents 2690 1790 :=
  segment 36 2690 1790 2726 0 (by rfl) (zero_represents 2726)

theorem cert_199404 : Represents 2528 2018 :=
  segment 162 2528 2018 2690 1790 (by rfl) cert_199242

theorem cert_199453 : Represents 2479 2477 :=
  segment 49 2479 2477 2528 2018 (by rfl) cert_199404

theorem cert_199470 : Represents 2480 2478 :=
  segment 16 2480 2478 2496 1866 (by rfl) cert_198116

theorem cert_199588 : Represents 2481 2479 :=
  segment 117 2481 2479 2598 2232 (by rfl) cert_190946

theorem cert_199605 : Represents 2482 2480 :=
  segment 16 2482 2480 2498 2078 (by rfl) cert_183815

theorem cert_199673 : Represents 2483 2481 :=
  segment 67 2483 2481 2550 1376 (by rfl) cert_193127

theorem cert_199724 : Represents 2484 2482 :=
  segment 50 2484 2482 2534 952 (by rfl) cert_197665

theorem cert_199736 : Represents 2485 2483 :=
  segment 11 2485 2483 2496 1792 (by rfl) cert_10879

theorem cert_199753 : Represents 2486 2484 :=
  segment 16 2486 2484 2502 0 (by rfl) (zero_represents 2502)

theorem cert_199882 : Represents 2504 210 :=
  segment 128 2504 210 2632 0 (by rfl) (zero_represents 2632)

theorem cert_199899 : Represents 2487 2485 :=
  segment 17 2487 2485 2504 210 (by rfl) cert_199882

theorem cert_199916 : Represents 2488 2486 :=
  segment 16 2488 2486 2504 210 (by rfl) cert_199882

theorem cert_199922 : Represents 2489 2487 :=
  segment 5 2489 2487 2494 2368 (by rfl) cert_193916

theorem cert_199959 : Represents 2490 2488 :=
  segment 36 2490 2488 2526 1128 (by rfl) cert_173751

theorem cert_199992 : Represents 3136 648 :=
  segment 32 3136 648 3168 386 (by rfl) cert_179915

theorem cert_200176 : Represents 2952 1578 :=
  segment 184 2952 1578 3136 648 (by rfl) cert_199992

theorem cert_200218 : Represents 2910 1104 :=
  segment 42 2910 1104 2952 1578 (by rfl) cert_200176

theorem cert_200240 : Represents 2888 1394 :=
  segment 22 2888 1394 2910 1104 (by rfl) cert_200218

theorem cert_200496 : Represents 2632 1426 :=
  segment 256 2632 1426 2888 1394 (by rfl) cert_200240

theorem cert_200506 : Represents 2622 2128 :=
  segment 10 2622 2128 2632 1426 (by rfl) cert_200496

theorem cert_200610 : Represents 2518 632 :=
  segment 104 2518 632 2622 2128 (by rfl) cert_200506

theorem cert_200637 : Represents 2491 2489 :=
  segment 27 2491 2489 2518 632 (by rfl) cert_200610

theorem cert_200642 : Represents 2492 2490 :=
  segment 4 2492 2490 2496 2434 (by rfl) cert_197456

theorem cert_200700 : Represents 2493 2491 :=
  segment 57 2493 2491 2550 1992 (by rfl) cert_196454

theorem cert_200745 : Represents 2494 2492 :=
  segment 44 2494 2492 2538 2038 (by rfl) cert_194944

theorem cert_200753 : Represents 2495 2493 :=
  segment 7 2495 2493 2502 1992 (by rfl) cert_198994

theorem cert_200764 : Represents 2496 2494 :=
  segment 10 2496 2494 2506 918 (by rfl) cert_40471

theorem cert_200772 : Represents 2497 2495 :=
  segment 7 2497 2495 2504 1994 (by rfl) cert_186759

theorem cert_200811 : Represents 2498 2496 :=
  segment 38 2498 2496 2536 618 (by rfl) cert_170820

theorem cert_200843 : Represents 2499 2497 :=
  segment 31 2499 2497 2530 2342 (by rfl) cert_196924

theorem cert_200884 : Represents 2558 1392 :=
  segment 40 2558 1392 2598 368 (by rfl) cert_180485

theorem cert_200942 : Represents 2500 2498 :=
  segment 58 2500 2498 2558 1392 (by rfl) cert_200884

theorem cert_200960 : Represents 2501 2499 :=
  segment 17 2501 2499 2518 632 (by rfl) cert_200610

theorem cert_201051 : Represents 2502 2500 :=
  segment 90 2502 2500 2592 2018 (by rfl) cert_193409

theorem cert_201079 : Represents 2503 2501 :=
  segment 27 2503 2501 2530 550 (by rfl) cert_176957

theorem cert_201086 : Represents 2504 2502 :=
  segment 6 2504 2502 2510 2256 (by rfl) cert_142399

theorem cert_201147 : Represents 2686 320 :=
  segment 60 2686 320 2746 1422 (by rfl) cert_184567

theorem cert_201175 : Represents 2658 2656 :=
  segment 28 2658 2656 2686 320 (by rfl) cert_201147

theorem cert_201241 : Represents 2592 1752 :=
  segment 66 2592 1752 2658 2656 (by rfl) cert_201175

theorem cert_201328 : Represents 2505 2503 :=
  segment 87 2505 2503 2592 1752 (by rfl) cert_201241

theorem cert_201391 : Represents 2507 2505 :=
  segment 61 2507 2505 2568 1792 (by rfl) cert_155722

theorem cert_201410 : Represents 2508 2506 :=
  segment 18 2508 2506 2526 1664 (by rfl) cert_197356

theorem cert_201481 : Represents 3418 1134 :=
  segment 70 3418 1134 3488 3200 (by rfl) cert_112817

theorem cert_201531 : Represents 3368 2912 :=
  segment 50 3368 2912 3418 1134 (by rfl) cert_201481

theorem cert_201561 : Represents 3338 1526 :=
  segment 30 3338 1526 3368 2912 (by rfl) cert_201531

theorem cert_201571 : Represents 3328 2658 :=
  segment 10 3328 2658 3338 1526 (by rfl) cert_201561

theorem cert_201595 : Represents 3304 384 :=
  segment 24 3304 384 3328 2658 (by rfl) cert_201571

theorem cert_201605 : Represents 3294 1664 :=
  segment 10 3294 1664 3304 384 (by rfl) cert_201595

theorem cert_201715 : Represents 3184 72 :=
  segment 110 3184 72 3294 1664 (by rfl) cert_201605

theorem cert_201721 : Represents 3178 2038 :=
  segment 6 3178 2038 3184 72 (by rfl) cert_201715

theorem cert_201755 : Represents 3144 1784 :=
  segment 34 3144 1784 3178 2038 (by rfl) cert_201721

theorem cert_201813 : Represents 3086 2064 :=
  segment 58 3086 2064 3144 1784 (by rfl) cert_201755

theorem cert_201971 : Represents 2928 2906 :=
  segment 158 2928 2906 3086 2064 (by rfl) cert_201813

theorem cert_201985 : Represents 2914 2502 :=
  segment 14 2914 2502 2928 2906 (by rfl) cert_201971

theorem cert_202241 : Represents 2658 1664 :=
  segment 256 2658 1664 2914 2502 (by rfl) cert_201985

theorem cert_202390 : Represents 2509 2507 :=
  segment 149 2509 2507 2658 1664 (by rfl) cert_202241

theorem cert_202393 : Represents 2510 2508 :=
  segment 2 2510 2508 2512 2498 (by rfl) cert_160018

theorem cert_202443 : Represents 2511 2509 :=
  segment 49 2511 2509 2560 608 (by rfl) cert_113745

theorem cert_202532 : Represents 2512 2510 :=
  segment 88 2512 2510 2600 2272 (by rfl) cert_182011

theorem cert_202642 : Represents 2513 2511 :=
  segment 109 2513 2511 2622 1520 (by rfl) cert_10753

theorem cert_202749 : Represents 2552 1850 :=
  segment 106 2552 1850 2658 2590 (by rfl) cert_184655

theorem cert_202787 : Represents 2514 2512 :=
  segment 38 2514 2512 2552 1850 (by rfl) cert_202749

theorem cert_202801 : Represents 2515 2513 :=
  segment 13 2515 2513 2528 66 (by rfl) cert_151498

theorem cert_202830 : Represents 2590 408 :=
  segment 28 2590 408 2618 14 (by rfl) cert_196153

theorem cert_202886 : Represents 2534 2528 :=
  segment 56 2534 2528 2590 408 (by rfl) cert_202830

theorem cert_202904 : Represents 2516 2514 :=
  segment 18 2516 2514 2534 2528 (by rfl) cert_202886

theorem cert_202956 : Represents 2517 2515 :=
  segment 51 2517 2515 2568 746 (by rfl) cert_119966

theorem cert_202977 : Represents 2518 2516 :=
  segment 20 2518 2516 2538 758 (by rfl) cert_182073

theorem cert_203010 : Represents 3136 2490 :=
  segment 32 3136 2490 3168 2784 (by rfl) cert_113137

theorem cert_203082 : Represents 3064 1544 :=
  segment 72 3064 1544 3136 2490 (by rfl) cert_203010

theorem cert_203162 : Represents 2984 2762 :=
  segment 80 2984 2762 3064 1544 (by rfl) cert_203082

theorem cert_203168 : Represents 2978 1254 :=
  segment 6 2978 1254 2984 2762 (by rfl) cert_203162

theorem cert_203236 : Represents 2910 1808 :=
  segment 68 2910 1808 2978 1254 (by rfl) cert_203168

theorem cert_203242 : Represents 2904 210 :=
  segment 6 2904 210 2910 1808 (by rfl) cert_203236

theorem cert_203258 : Represents 2888 1496 :=
  segment 16 2888 1496 2904 210 (by rfl) cert_203242

theorem cert_203298 : Represents 2848 34 :=
  segment 40 2848 34 2888 1496 (by rfl) cert_203258

theorem cert_203328 : Represents 2818 222 :=
  segment 30 2818 222 2848 34 (by rfl) cert_203298

theorem cert_203584 : Represents 2562 1128 :=
  segment 256 2562 1128 2818 222 (by rfl) cert_203328

theorem cert_203596 : Represents 2550 504 :=
  segment 12 2550 504 2562 1128 (by rfl) cert_203584

theorem cert_203627 : Represents 2519 2517 :=
  segment 31 2519 2517 2550 504 (by rfl) cert_203596

theorem cert_203666 : Represents 2520 2518 :=
  segment 38 2520 2518 2558 1392 (by rfl) cert_200884

theorem cert_203674 : Represents 2521 2519 :=
  segment 7 2521 2519 2528 2018 (by rfl) cert_199404

theorem cert_203735 : Represents 2682 1614 :=
  segment 60 2682 1614 2742 888 (by rfl) cert_188133

theorem cert_203895 : Represents 2522 2520 :=
  segment 160 2522 2520 2682 1614 (by rfl) cert_203735

theorem cert_203899 : Represents 2523 2521 :=
  segment 3 2523 2521 2526 2496 (by rfl) cert_186737

theorem cert_203930 : Represents 2524 2522 :=
  segment 30 2524 2522 2554 2190 (by rfl) cert_10821

theorem cert_203956 : Represents 2525 2523 :=
  segment 25 2525 2523 2550 1864 (by rfl) cert_188647

theorem cert_203991 : Represents 2526 2524 :=
  segment 34 2526 2524 2560 1632 (by rfl) cert_171417

theorem cert_204051 : Represents 2527 2525 :=
  segment 59 2527 2525 2586 142 (by rfl) cert_10789

theorem cert_204060 : Represents 2848 1384 :=
  segment 8 2848 1384 2856 800 (by rfl) cert_10519

theorem cert_204316 : Represents 2592 2200 :=
  segment 256 2592 2200 2848 1384 (by rfl) cert_204060

theorem cert_204348 : Represents 2560 1050 :=
  segment 32 2560 1050 2592 2200 (by rfl) cert_204316

theorem cert_204380 : Represents 2528 2526 :=
  segment 32 2528 2526 2560 1050 (by rfl) cert_204348

theorem cert_204404 : Represents 2529 2527 :=
  segment 23 2529 2527 2552 1850 (by rfl) cert_202749

theorem cert_204413 : Represents 2744 2408 :=
  segment 8 2744 2408 2752 1440 (by rfl) cert_19760

theorem cert_204533 : Represents 2624 2594 :=
  segment 120 2624 2594 2744 2408 (by rfl) cert_204413

theorem cert_204557 : Represents 2600 394 :=
  segment 24 2600 394 2624 2594 (by rfl) cert_204533

theorem cert_204627 : Represents 2530 2528 :=
  segment 70 2530 2528 2600 394 (by rfl) cert_204557

theorem cert_204665 : Represents 2531 2529 :=
  segment 37 2531 2529 2568 778 (by rfl) cert_75520

theorem cert_204720 : Represents 2648 1376 :=
  segment 54 2648 1376 2702 192 (by rfl) cert_141278

theorem cert_204750 : Represents 2618 2446 :=
  segment 30 2618 2446 2648 1376 (by rfl) cert_204720

theorem cert_204836 : Represents 2532 2530 :=
  segment 86 2532 2530 2618 2446 (by rfl) cert_204750

theorem cert_204838 : Represents 2533 2531 :=
  segment 1 2533 2531 2534 2528 (by rfl) cert_202886

theorem cert_204881 : Represents 2534 2532 :=
  segment 42 2534 2532 2576 1816 (by rfl) cert_113729

theorem cert_204907 : Represents 2535 2533 :=
  segment 25 2535 2533 2560 1050 (by rfl) cert_204348

theorem cert_204932 : Represents 2536 2534 :=
  segment 24 2536 2534 2560 64 (by rfl) cert_197639

theorem cert_204999 : Represents 2862 2568 :=
  segment 66 2862 2568 2928 2906 (by rfl) cert_201971

theorem cert_205055 : Represents 2806 2328 :=
  segment 56 2806 2328 2862 2568 (by rfl) cert_204999

theorem cert_205083 : Represents 2778 974 :=
  segment 28 2778 974 2806 2328 (by rfl) cert_205055

theorem cert_205139 : Represents 2722 486 :=
  segment 56 2722 486 2778 974 (by rfl) cert_205083

theorem cert_205197 : Represents 2664 202 :=
  segment 58 2664 202 2722 486 (by rfl) cert_205139

theorem cert_205324 : Represents 2537 2535 :=
  segment 127 2537 2535 2664 202 (by rfl) cert_205197

theorem cert_205339 : Represents 2538 2536 :=
  segment 14 2538 2536 2552 730 (by rfl) cert_40425

theorem cert_205398 : Represents 2856 448 :=
  segment 58 2856 448 2914 2110 (by rfl) cert_176573

theorem cert_205414 : Represents 2840 2226 :=
  segment 16 2840 2226 2856 448 (by rfl) cert_205398

theorem cert_205526 : Represents 2728 2602 :=
  segment 112 2728 2602 2840 2226 (by rfl) cert_205414

theorem cert_205662 : Represents 2592 736 :=
  segment 136 2592 736 2728 2602 (by rfl) cert_205526

theorem cert_205715 : Represents 2539 2537 :=
  segment 53 2539 2537 2592 736 (by rfl) cert_205662

theorem cert_205718 : Represents 2540 2538 :=
  segment 2 2540 2538 2542 2528 (by rfl) cert_158633

theorem cert_205728 : Represents 2541 2539 :=
  segment 9 2541 2539 2550 504 (by rfl) cert_203596

theorem cert_205739 : Represents 2542 2540 :=
  segment 10 2542 2540 2552 1010 (by rfl) cert_142357

theorem cert_205759 : Represents 2543 2541 :=
  segment 19 2543 2541 2562 1926 (by rfl) cert_196442

theorem cert_205806 : Represents 2624 258 :=
  segment 46 2624 258 2670 1072 (by rfl) cert_184643

theorem cert_205814 : Represents 2616 1330 :=
  segment 8 2616 1330 2624 258 (by rfl) cert_205806

theorem cert_205886 : Represents 2544 2542 :=
  segment 72 2544 2542 2616 1330 (by rfl) cert_205814

theorem cert_205966 : Represents 2545 2543 :=
  segment 79 2545 2543 2624 98 (by rfl) cert_182764

theorem cert_206091 : Represents 2546 2544 :=
  segment 124 2546 2544 2670 1600 (by rfl) cert_176817

theorem cert_206145 : Represents 2547 2545 :=
  segment 53 2547 2545 2600 394 (by rfl) cert_204557

theorem cert_206220 : Represents 2548 2546 :=
  segment 74 2548 2546 2622 1104 (by rfl) cert_19890

theorem cert_206230 : Represents 2549 2547 :=
  segment 9 2549 2547 2558 512 (by rfl) cert_197746

theorem cert_206239 : Represents 2840 626 :=
  segment 8 2840 626 2848 1016 (by rfl) cert_181763

theorem cert_206335 : Represents 2744 360 :=
  segment 96 2744 360 2840 626 (by rfl) cert_206239

theorem cert_206413 : Represents 2666 438 :=
  segment 78 2666 438 2744 360 (by rfl) cert_206335

theorem cert_206529 : Represents 2550 2548 :=
  segment 116 2550 2548 2666 438 (by rfl) cert_206413

theorem cert_206545 : Represents 2551 2549 :=
  segment 15 2551 2549 2566 2136 (by rfl) cert_143850

theorem cert_206584 : Represents 2552 2550 :=
  segment 38 2552 2550 2590 408 (by rfl) cert_202830

theorem cert_206664 : Represents 2553 2551 :=
  segment 79 2553 2551 2632 1880 (by rfl) cert_198799

theorem cert_206735 : Represents 2554 2552 :=
  segment 70 2554 2552 2624 258 (by rfl) cert_205806

theorem cert_206771 : Represents 2555 2553 :=
  segment 35 2555 2553 2590 1232 (by rfl) cert_196864

theorem cert_206790 : Represents 2556 2554 :=
  segment 18 2556 2554 2574 1160 (by rfl) cert_151452

theorem cert_206799 : Represents 2656 2626 :=
  segment 8 2656 2626 2664 2464 (by rfl) cert_178140

theorem cert_206898 : Represents 2557 2555 :=
  segment 99 2557 2555 2656 2626 (by rfl) cert_206799

theorem cert_206999 : Represents 2558 2556 :=
  segment 100 2558 2556 2658 806 (by rfl) cert_188539

theorem cert_207071 : Represents 2559 2557 :=
  segment 71 2559 2557 2630 728 (by rfl) cert_124342

theorem cert_207158 : Represents 2560 2558 :=
  segment 86 2560 2558 2646 1992 (by rfl) cert_182742

theorem cert_207204 : Represents 2561 2559 :=
  segment 45 2561 2559 2606 1240 (by rfl) cert_164486

theorem cert_207215 : Represents 2590 1344 :=
  segment 10 2590 1344 2600 330 (by rfl) cert_171377

theorem cert_207243 : Represents 2562 2560 :=
  segment 28 2562 2560 2590 1344 (by rfl) cert_207215

theorem cert_207260 : Represents 4472 90 :=
  segment 16 4472 90 4488 0 (by rfl) (zero_represents 4488)

theorem cert_207276 : Represents 4456 2688 :=
  segment 16 4456 2688 4472 90 (by rfl) cert_207260

theorem cert_207332 : Represents 4400 106 :=
  segment 56 4400 106 4456 2688 (by rfl) cert_207276

theorem cert_207342 : Represents 4390 4096 :=
  segment 10 4390 4096 4400 106 (by rfl) cert_207332

theorem cert_207382 : Represents 4350 752 :=
  segment 40 4350 752 4390 4096 (by rfl) cert_207342

theorem cert_207444 : Represents 4288 864 :=
  segment 62 4288 864 4350 752 (by rfl) cert_207382

theorem cert_207452 : Represents 4280 3432 :=
  segment 8 4280 3432 4288 864 (by rfl) cert_207444

theorem cert_207494 : Represents 4238 1840 :=
  segment 42 4238 1840 4280 3432 (by rfl) cert_207452

theorem cert_207518 : Represents 4214 3248 :=
  segment 24 4214 3248 4238 1840 (by rfl) cert_207494

theorem cert_207540 : Represents 4192 3144 :=
  segment 22 4192 3144 4214 3248 (by rfl) cert_207518

theorem cert_207602 : Represents 4130 862 :=
  segment 62 4130 862 4192 3144 (by rfl) cert_207540

theorem cert_207604 : Represents 4128 1248 :=
  segment 2 4128 1248 4130 862 (by rfl) cert_207602

theorem cert_207766 : Represents 3966 3904 :=
  segment 162 3966 3904 4128 1248 (by rfl) cert_207604

theorem cert_207796 : Represents 3936 992 :=
  segment 30 3936 992 3966 3904 (by rfl) cert_207766

theorem cert_207804 : Represents 3928 434 :=
  segment 8 3928 434 3936 992 (by rfl) cert_207796

theorem cert_207996 : Represents 3736 1010 :=
  segment 192 3736 1010 3928 434 (by rfl) cert_207804

theorem cert_208076 : Represents 3656 2634 :=
  segment 80 3656 2634 3736 1010 (by rfl) cert_207996

theorem cert_208092 : Represents 3640 2842 :=
  segment 16 3640 2842 3656 2634 (by rfl) cert_208076

theorem cert_208146 : Represents 3586 990 :=
  segment 54 3586 990 3640 2842 (by rfl) cert_208092

theorem cert_208204 : Represents 3528 1266 :=
  segment 58 3528 1266 3586 990 (by rfl) cert_208146

theorem cert_208404 : Represents 3328 2176 :=
  segment 200 3328 2176 3528 1266 (by rfl) cert_208204

theorem cert_208420 : Represents 3312 696 :=
  segment 16 3312 696 3328 2176 (by rfl) cert_208404

theorem cert_208444 : Represents 3288 1920 :=
  segment 24 3288 1920 3312 696 (by rfl) cert_208420

theorem cert_208666 : Represents 3066 1742 :=
  segment 222 3066 1742 3288 1920 (by rfl) cert_208444

theorem cert_208724 : Represents 3008 2498 :=
  segment 58 3008 2498 3066 1742 (by rfl) cert_208666

theorem cert_208762 : Represents 2970 1230 :=
  segment 38 2970 1230 3008 2498 (by rfl) cert_208724

theorem cert_208780 : Represents 2952 728 :=
  segment 18 2952 728 2970 1230 (by rfl) cert_208762

theorem cert_208818 : Represents 2914 806 :=
  segment 38 2914 806 2952 728 (by rfl) cert_208780

theorem cert_208822 : Represents 2910 2416 :=
  segment 4 2910 2416 2914 806 (by rfl) cert_208818

theorem cert_208826 : Represents 2906 878 :=
  segment 4 2906 878 2910 2416 (by rfl) cert_208822

theorem cert_208844 : Represents 2888 2328 :=
  segment 18 2888 2328 2906 878 (by rfl) cert_208826

theorem cert_208876 : Represents 2856 2410 :=
  segment 32 2856 2410 2888 2328 (by rfl) cert_208844

theorem cert_208892 : Represents 2840 616 :=
  segment 16 2840 616 2856 2410 (by rfl) cert_208876

theorem cert_209108 : Represents 2624 2370 :=
  segment 216 2624 2370 2840 616 (by rfl) cert_208892

theorem cert_209169 : Represents 2563 2561 :=
  segment 61 2563 2561 2624 2370 (by rfl) cert_209108

theorem cert_209206 : Represents 2564 2562 :=
  segment 36 2564 2562 2600 1386 (by rfl) cert_197949

theorem cert_209232 : Represents 2565 2563 :=
  segment 25 2565 2563 2590 1344 (by rfl) cert_207215

theorem cert_209289 : Represents 2690 262 :=
  segment 56 2690 262 2746 1326 (by rfl) cert_176741

theorem cert_209413 : Represents 2566 2564 :=
  segment 124 2566 2564 2690 262 (by rfl) cert_209289

theorem cert_209463 : Represents 2567 2565 :=
  segment 49 2567 2565 2616 1330 (by rfl) cert_205814

theorem cert_209568 : Represents 2568 2566 :=
  segment 104 2568 2566 2672 1016 (by rfl) cert_172375

theorem cert_209592 : Represents 2569 2567 :=
  segment 23 2569 2567 2592 736 (by rfl) cert_205662

theorem cert_209601 : Represents 2656 32 :=
  segment 8 2656 32 2664 202 (by rfl) cert_205197

theorem cert_209673 : Represents 2584 1562 :=
  segment 72 2584 1562 2656 32 (by rfl) cert_209601

theorem cert_209687 : Represents 2570 2568 :=
  segment 14 2570 2568 2584 1562 (by rfl) cert_209673

theorem cert_209944 : Represents 2672 1320 :=
  segment 256 2672 1320 2928 24 (by rfl) cert_177876

theorem cert_209952 : Represents 2664 2098 :=
  segment 8 2664 2098 2672 1320 (by rfl) cert_209944

theorem cert_210045 : Represents 2571 2569 :=
  segment 93 2571 2569 2664 2098 (by rfl) cert_209952

theorem cert_210196 : Represents 2572 2570 :=
  segment 150 2572 2570 2722 222 (by rfl) cert_191723

theorem cert_210208 : Represents 2573 2571 :=
  segment 11 2573 2571 2584 2144 (by rfl) cert_197094

theorem cert_210293 : Represents 2574 2572 :=
  segment 84 2574 2572 2658 550 (by rfl) cert_129886

end Erdos261Finite
