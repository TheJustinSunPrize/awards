import ReciprocalDoubling
open ReciprocalDoubling
#eval (List.range 11).map S
#eval (List.range 10).map isIrreducible
#eval (List.range 8).map numeratorBound
#eval (List.range 8).map (fun m => [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31].map (isCompatible m))
