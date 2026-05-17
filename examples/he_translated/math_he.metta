; Translated from PeTTa to HE (38 atoms)
; Source: examples/math.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(assertEqualToEval (pow-math 2 3) 8.0)
!(assertEqualToEval (sqrt-math 9) 3.0)
!(assertEqualToEval (abs-math -5) 5)
!(assertEqualToEval (log-math 10 100) 2.0)
!(assertEqualToEval (trunc-math 5.6) 5.0)
!(assertEqualToEval (ceil-math 5.2) 6.0)
!(assertEqualToEval (floor-math 5.8) 5.0)
!(assertEqualToEval (round-math 5.4) 5.0)
!(assertEqualToEval (round-math 5.6) 6.0)
!(assertEqualToEval (sin-math 0) 0.0)
!(assertEqualToEval (asin-math 0) 0.0)
!(assertEqualToEval (cos-math 0) 1.0)
!(assertEqualToEval (acos-math 1) 0.0)
!(assertEqualToEval (tan-math 0) 0.0)
!(assertEqualToEval (atan-math 0) 0.0)
!(assertEqualToEval (isnan-math 0.0) False)
!(assertEqualToEval (isinf-math 0.0) False)
!(assertEqualToEval (min-atom (2 6 7 4 9 3)) 2.0)
!(assertEqualToEval (max-atom (2 6 7 4 9 3)) 9.0)
