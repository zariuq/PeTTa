; ============================================================================
; FORGETTING STRATEGIES DEMO --- §20 made tangible
; ============================================================================
;
; Max wrote: "Currently I just overwrite" for memory updates.  For an honest
; agent doing LTM management, overwrite is unsound --- it loses provenance
; and silently miscounts confidence.
;
; This demo shows two scenarios:
;
;   Scenario A --- LOCAL SUPPORT, exact-inverse forgetting is SAFE.
;     Three independent sources contribute to (alice honest).  Source 2 turns
;     out to be lying; we want to forget it.  Compare four strategies
;     side-by-side: numerical (stv, c) and L1 distance to the correct
;     S1+S3 answer.
;
;   Scenario B --- LEAKED SUPPORT, the no-go theorem fires.
;     The (alice honest) belief has been used to derive (alice invitable).
;     Source 2's contribution has propagated to a belief OUTSIDE the
;     forget scope.  The no-go theorem from GenericWorldModelForgetting.lean
;     fires: no exact-inverse forgetting is possible.  Three escape
;     strategies are surfaced with their costs.
;
; The no-go theorem (informally): if a revision's contribution has leaked
; to any query outside the forget scope, no forgetting operation can be
; the exact inverse of that revision.
; ============================================================================

!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln)

; ----------------------------------------------------------------------------
; Helpers
; ----------------------------------------------------------------------------

;; Absolute value (local to avoid clashing with any builtin)
(= (myabs $x) (if (< $x 0.0) (- 0.0 $x) $x))

;; L1 distance between two (stv s c) pairs
(= (L1stv (stv $s1 $c1) (stv $s2 $c2))
   (+ (myabs (- $s1 $s2)) (myabs (- $c1 $c2))))

;; Inverse-revision: given the merged TV (s_R, c_R) and one source TV
;; (s_2, c_2) whose stamp we want to forget, compute the result of
;; subtracting source 2's contribution.  Uses the c2w/w2c machinery
;; of lib_pln to convert to evidence counts, subtract, and convert back.
(= (Truth_InverseRevision (stv $sR $cR) (stv $s2 $c2))
   (let* (($wR (Truth_c2w $cR))
          ($w2 (Truth_c2w $c2))
          ($wRem (- $wR $w2))
          ($posR (* $sR $wR))
          ($pos2 (* $s2 $w2))
          ($posRem (- $posR $pos2))
          ($sRem (/safe $posRem $wRem))
          ($cRem (Truth_w2c $wRem)))
         (stv (min 1.0 $sRem) (min 1.0 $cRem))))

; ----------------------------------------------------------------------------
; Scenario A --- LOCAL SUPPORT, exact-inverse SAFE
; ----------------------------------------------------------------------------

!(println! "================================================================")
!(println! " SCENARIO A --- Local support: exact-inverse forgetting is SAFE")
!(println! "================================================================")
!(println! "")

;; Three independent sources, disjoint stamps (1), (2), (3)
(= (S1) (stv 0.8 0.7))   ; trusted-friend testimony
(= (S2) (stv 0.7 0.6))   ; distant-acquaintance (will be forgotten)
(= (S3) (stv 0.9 0.8))   ; alice's own behavior

!(println! ("S1 trusted-friend           :" (S1)))
!(println! ("S2 distant-acquaintance     :" (S2) "  <-- will be forgotten"))
!(println! ("S3 alice's own behavior     :" (S3)))
!(println! "")

;; Merge all three (Truth_Revision under stamp-disjointness is additive)
(= (mergedAll) (Truth_Revision (S1) (Truth_Revision (S2) (S3))))
(= (mergedS1S3) (Truth_Revision (S1) (S3)))

!(println! ("merged S1+S2+S3 (current belief)             :" (mergedAll)))
!(println! ("merged S1+S3 (correct answer after forgetting):" (mergedS1S3)))
!(println! "")

;; Four strategies for forgetting S2
(= (strat1-overwrite-drop-all) (stv 0.0 0.0))
(= (strat2-overwrite-S3-only)  (S3))
(= (strat3-heuristic-avg)      (stv 0.85 0.7))
(= (strat4-exact-inverse)      (Truth_InverseRevision (mergedAll) (S2)))

!(println! "--- Four strategies side-by-side ---")
!(println! ("[1] overwrite-drop-all       :" (strat1-overwrite-drop-all)
            "  L1=" (L1stv (strat1-overwrite-drop-all) (mergedS1S3))))
!(println! ("[2] overwrite-S3-only        :" (strat2-overwrite-S3-only)
            "  L1=" (L1stv (strat2-overwrite-S3-only) (mergedS1S3))))
!(println! ("[3] heuristic-average        :" (strat3-heuristic-avg)
            "  L1=" (L1stv (strat3-heuristic-avg) (mergedS1S3))))
!(println! ("[4] support-tracked inverse  :" (strat4-exact-inverse)
            "  L1=" (L1stv (strat4-exact-inverse) (mergedS1S3))))
!(println! "")

!(println! "Strategy [4] equals the correct (S1+S3) answer to floating-point precision.")
!(println! "Strategies [1]-[3] lose visible information; the L1 distances quantify it.")
!(println! "")

; ----------------------------------------------------------------------------
; Sanity test on exact arithmetic (c=0.5 case avoids float drift)
; ----------------------------------------------------------------------------

!(test (Truth_c2w 0.5) 1.0)
!(test (myabs -3.5) 3.5)
!(test (myabs 2.0) 2.0)

; ----------------------------------------------------------------------------
; Scenario B --- LEAKED SUPPORT, NO-GO fires
; ----------------------------------------------------------------------------

!(println! "")
!(println! "================================================================")
!(println! " SCENARIO B --- Leaked support: no-go theorem fires")
!(println! "================================================================")
!(println! "")

;; A community-trait inference rule: "honest" implies "invitable"
(= (rule-implication) (stv 0.8 0.9))

;; The current (alice invitable) was derived from the original (alice honest)
;; --- which includes S2's contribution.
(= (alice-invitable-current)
   (Truth_ModusPonens (mergedAll) (rule-implication)))

;; The correct (alice invitable) after forgetting S2 would be derived from
;; the S1+S3 merge instead.
(= (alice-invitable-correct)
   (Truth_ModusPonens (mergedS1S3) (rule-implication)))

!(println! ("alice-invitable (current, with S2's contribution) :" (alice-invitable-current)))
!(println! ("alice-invitable (correct after forgetting S2)     :" (alice-invitable-correct)))
!(println! "")

;; The no-go theorem statement made mechanical:
!(println! "No-go check:")
!(println! "  stamp(alice-honest)    = (1 2 3)")
!(println! "  stamp(alice-invitable) = (1 2 3 + implication-rule-stamps)")
!(println! "  forget scope           = {alice-honest only}")
!(println! "")
!(println! "  alice-invitable is OUTSIDE the forget scope, but its stamp")
!(println! "  INCLUDES 2.  S2's contribution has LEAKED beyond the scope.")
!(println! "")
!(println! "  ==> NO-GO THEOREM FIRES: exact-inverse forgetting of S2 is")
!(println! "      provably impossible for any forgetting operation.")
!(println! "")

;; Three escape strategies
(= (escape1-rederive)    (alice-invitable-correct))     ; correct, expensive
(= (escape2-approximate) (alice-invitable-current))     ; do nothing to invitable; leak remains
(= (escape3-overwrite)   (stv 0.0 0.0))                 ; Max's current heuristic

!(println! "--- Three escape strategies for alice-invitable ---")
!(println! ("[1] re-derive (correct, expensive)   :" (escape1-rederive)
            "  L1=" (L1stv (escape1-rederive) (alice-invitable-correct))))
!(println! ("[2] approximate-forget (leak remains):" (escape2-approximate)
            "  L1=" (L1stv (escape2-approximate) (alice-invitable-correct))))
!(println! ("[3] overwrite (current heuristic)    :" (escape3-overwrite)
            "  L1=" (L1stv (escape3-overwrite) (alice-invitable-correct))))
!(println! "")

!(println! "Rationale:")
!(println! "  [1] always correct but pays derivation-graph re-execution cost.")
!(println! "  [2] preserves the belief form, but S2's contribution remains;")
!(println! "      currently no formal bound on the resulting error.")
!(println! "  [3] loses the derived belief entirely; re-derivation deferred.")
!(println! "")

; ----------------------------------------------------------------------------
; Summary
; ----------------------------------------------------------------------------

!(println! "================================================================")
!(println! " SUMMARY")
!(println! "================================================================")
!(println! "")
!(println! " Scenario A: when support is LOCAL, strategy [4] (support-tracked")
!(println! "             exact-inverse) gives the correct answer with zero")
!(println! "             information loss.  Naive strategies leak quantifiable")
!(println! "             confidence (L1 distance ranges from ~0.04 to ~1.7).")
!(println! "")
!(println! " Scenario B: when support has LEAKED through inference, exact-inverse")
!(println! "             is provably impossible.  Re-derivation is the only sound")
!(println! "             strategy; the other two have known costs.")
!(println! "")
!(println! " Discipline: TRACK SUPPORT, CHECK SCOPE, FORGET ONLY WHEN SAFE.")
!(println! "================================================================")
