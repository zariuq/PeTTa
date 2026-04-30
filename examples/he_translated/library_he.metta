; Translated from PeTTa to HE (4 atoms)
; Source: /home/zar/claude/hyperon/petta-he-profile/examples/library.metta
; Translation target: PeTTa HE
; Intended runtime: ./run.sh --he
; Portability: portable/default HE lowering

!(import! &self (library lib_roman))
!(assertPeTTaTest (map-flat (+ 1) (1 2 3)) (2 3 4))
