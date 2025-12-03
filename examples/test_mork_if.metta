; Test IF/ELSE conditional using MORK exec rules
; Priority 0 (true branch) fires when condition-holds is present
; Priority 1 (else branch) fires otherwise

!(import! &self ../lib/lib_he)

; Setup
!(add-atom &mork (if-run))
!(add-atom &mork (condition-holds))

; True branch: priority 0
!(add-atom &mork
  (exec (0 if-true)
    (, (if-run) (condition-holds))
    (O (+ (result then-branch))
       (- (if-run)))))

; Else branch: priority 1
!(add-atom &mork
  (exec (1 if-false)
    (, (if-run))
    (O (+ (result else-branch))
       (- (if-run)))))

; Execute and test
!(mm2-exec &mork 2)
!(test (collapse (match &mork (result $x) $x))
       (then-branch))
