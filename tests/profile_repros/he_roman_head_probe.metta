; Minimal repro for the roman reverse-pattern regression under --he.
; Default PeTTa returns 1 here; current --he returns ().

!(import! &self ../../lib/lib_roman.metta)
!(println! "DEBUG: before-head")
!(assertPeTTaTest (let (head $x) (1 2 3) $x) 1)
!(println! "DEBUG: after-head")
