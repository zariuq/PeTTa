; Test file for Frame Management (PeTTa version)
; Testing push-frame and pop-frame with realistic scenarios

!(import! &self ../lib/lib_he)
; Note: NOT importing helpers_petta to avoid test pollution


; ===== Function Definitions (Inline for Testing) =====

; adjust-state-additive: Add to state
(= (adjust-state-additive $state $delta)
  (let $current (get-state $state)
    (change-state! $state (+ $current $delta))))

; adjust-state-subtractive: Subtract from state
(= (adjust-state-subtractive $state $delta)
  (let $current (get-state $state)
    (change-state! $state (- $current $delta))))

; push-frame: Increment frame depth
(= (push-frame $fd)
  (adjust-state-additive $fd 1))

; pop-frame: Pop frame and remove all data at current level
; PeTTa adaptation: uses &self with KB tag instead of separate $kb parameter
(= (pop-frame $kb-tag $fd)
  (let $level (get-state $fd)
    (progn
      ; Remove EList at current level
      (collapse (match &self ($kb-tag (EList (FSDepth $level) $elist))
                  (remove-atom &self ($kb-tag (EList (FSDepth $level) $elist)))))
      ; Remove FList at current level
      (collapse (match &self ($kb-tag (FList (FSDepth $level) $flist))
                  (remove-atom &self ($kb-tag (FList (FSDepth $level) $flist)))))
      ; Remove all other data at current level (Var, DVar, etc.)
      (collapse (match &self ($kb-tag ($any1 $any2 (FSDepth $level) $data))
                  (remove-atom &self ($kb-tag ($any1 $any2 (FSDepth $level) $data)))))
      ; Decrement frame depth
      (adjust-state-subtractive $fd 1))))

; ===== Tests =====

!(println! "=== Testing Frame Management ===")
!(println! "")

!(println! "Test 1: push-frame increments state")
!(bind! &fd1 (new-state 0))
!(push-frame &fd1)
!(test (get-state &fd1) 1)

!(println! "Test 2: Multiple push-frames")
!(push-frame &fd1)
!(push-frame &fd1)
!(test (get-state &fd1) 3)

!(println! "Test 3: pop-frame removes EList at current level")
!(bind! &fd3 (new-state 0))
!(push-frame &fd3)
!(add-atom &self (KB3 (EList (FSDepth 1) ((|- P)))))
!(test   (collapse (match &self (KB3 (EList (FSDepth $l) $e)) $l))
  (1))
!(pop-frame KB3 &fd3)
!(test   (collapse (match &self (KB3 (EList (FSDepth $l) $e)) $l))
  ())

!(println! "Test 4: pop-frame removes FList at current level")
!(bind! &fd4 (new-state 0))
!(push-frame &fd4)
!(add-atom &self (KB4 (FList (FSDepth 1) ((wff P)))))
!(test   (collapse (match &self (KB4 (FList (FSDepth $l) $f)) $l))
  (1))
!(pop-frame KB4 &fd4)
!(test   (collapse (match &self (KB4 (FList (FSDepth $l) $f)) $l))
  ())

!(println! "Test 5: pop-frame removes Var at current level")
!(bind! &fd5 (new-state 0))
!(push-frame &fd5)
!(add-atom &self (KB5 (Var x (FSDepth 1) (Type "$v"))))
!(add-atom &self (KB5 (Var y (FSDepth 1) (Type "$v"))))
!(test   (collapse (match &self (KB5 (Var $v (FSDepth 1) (Type "$v"))) $v))
  (x y))
!(pop-frame KB5 &fd5)
!(test   (collapse (match &self (KB5 (Var $v (FSDepth 1) (Type "$v"))) $v))
  ())

!(println! "Test 6: pop-frame preserves lower levels")
!(bind! &fd6 (new-state 0))
; Add at level 0
!(add-atom &self (KB6 (Var a (FSDepth 0) (Type "$v"))))
!(push-frame &fd6)
; Add at level 1
!(add-atom &self (KB6 (Var b (FSDepth 1) (Type "$v"))))
!(push-frame &fd6)
; Add at level 2
!(add-atom &self (KB6 (Var c (FSDepth 2) (Type "$v"))))
; Pop level 2
!(pop-frame KB6 &fd6)
; Level 0 and 1 should remain
!(test   (collapse (match &self (KB6 (Var a (FSDepth 0) (Type "$v"))) a))
  (a))
!(test   (collapse (match &self (KB6 (Var b (FSDepth 1) (Type "$v"))) b))
  (b))
!(test   (collapse (match &self (KB6 (Var c (FSDepth 2) (Type "$v"))) c))
  ())

!(println! "Test 7: pop-frame decrements frame depth")
!(bind! &fd7 (new-state 0))
!(push-frame &fd7)
!(push-frame &fd7)
!(test (get-state &fd7) 2)
!(pop-frame KB7 &fd7)
!(test (get-state &fd7) 1)
!(pop-frame KB7 &fd7)
!(test (get-state &fd7) 0)

!(println! "Test 8: Multiple push/pop sequence")
!(bind! &fd8 (new-state 0))
!(push-frame &fd8)
!(add-atom &self (KB8 (Var x (FSDepth 1) (Type "$v"))))
!(push-frame &fd8)
!(add-atom &self (KB8 (Var y (FSDepth 2) (Type "$v"))))
!(pop-frame KB8 &fd8)
; y should be gone, x should remain
!(test   (collapse (match &self (KB8 (Var y (FSDepth 2) (Type "$v"))) y))
  ())
!(test   (collapse (match &self (KB8 (Var x (FSDepth 1) (Type "$v"))) x))
  (x))
!(pop-frame KB8 &fd8)
; x should now be gone
!(test   (collapse (match &self (KB8 (Var x (FSDepth 1) (Type "$v"))) x))
  ())

!(println! "")
!(println! "=== All frame management tests complete ===")
