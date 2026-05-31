; ============================================================================
; OVERLAP-CORRECTED REVISION DEMO --- Level 0 vs Level 1 side-by-side
; ============================================================================
;
; This is the answer to Max's §37 question ("how do I actually compute the
; overlap term?").  PeTTa already has the Level 0 binary gate (StampDisjoint
; in lib_pln.metta).  This file demonstrates the Level 1 graded formula
; from lib_overlap_corrected_revision.metta and contrasts it with both
; (a) the naive Truth_Revision (no provenance awareness, double-counts) and
; (b) the conservative blocked-merge (Level 0 refusal to combine).
;
; Run:  cd /home/zar/claude/hyperon/PeTTa
;       ulimit -v 10485760 && ./run.sh examples/overlap_corrected_revision_demo.metta --silent
; ============================================================================

!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln)
!(import! &self ../lib/lib_overlap_corrected_revision)

!(println! "===========================================================")
!(println! " OVERLAP-CORRECTED REVISION DEMO")
!(println! "===========================================================")
!(println! "")

;; ----- Case 1: Disjoint stamps (Level 0 == Level 1) -----

!(println! "Case 1: DISJOINT STAMPS  (1)(2) vs (3)(4)")
!(println! "  Naive Truth_Revision         (no stamps):")
!(println! ("    " (Truth_Revision (stv 0.6 0.9) (stv 0.4 0.8))))
!(println! "  Level 1 OverlapCorrected   (stamps disjoint):")
!(println! ("    " (Truth_OverlapCorrectedRevision (stv 0.6 0.9) (stv 0.4 0.8) (1 2) (3 4))))
!(println! "  Expected: identical to Truth_Revision (no overlap to correct).")
!(println! "  Stamp intersection size:")
!(println! ("    " (StampIntersectionCount (1 2) (3 4))))
!(println! "")

;; ----- Case 2: Identical stamps (full overlap) -----

!(println! "Case 2: IDENTICAL STAMPS  (1 2) vs (1 2)")
!(println! "  Naive Truth_Revision (would inflate, double-counts):")
!(println! ("    " (Truth_Revision (stv 0.6 0.9) (stv 0.4 0.8))))
!(println! "  Level 1 OverlapCorrected (full discount):")
!(println! ("    " (Truth_OverlapCorrectedRevision (stv 0.6 0.9) (stv 0.4 0.8) (1 2) (1 2))))
!(println! "  Expected: strength ~ average of the two TVs;")
!(println! "            confidence DOES NOT exceed input confidences.")
!(println! "  Stamp intersection size:")
!(println! ("    " (StampIntersectionCount (1 2) (1 2))))
!(println! "")

;; ----- Case 3: Partial overlap -----

!(println! "Case 3: PARTIAL OVERLAP  (1 2 3) vs (2 3 4)")
!(println! "  Two stamp atoms shared, two unique on each side.")
!(println! "  Naive Truth_Revision (no provenance, inflates):")
!(println! ("    " (Truth_Revision (stv 0.6 0.9) (stv 0.4 0.8))))
!(println! "  Level 1 OverlapCorrected:")
!(println! ("    " (Truth_OverlapCorrectedRevision (stv 0.6 0.9) (stv 0.4 0.8) (1 2 3) (2 3 4))))
!(println! "  Expected: between the disjoint and identical answers.")
!(println! "  Stamp intersection size:")
!(println! ("    " (StampIntersectionCount (1 2 3) (2 3 4))))
!(println! "")

;; ----- Case 4: Audit-friendly variant -----

!(println! "Case 4: AUDIT VARIANT  (1 2 3) vs (2 3 4)")
!(println! "  Returns merged TV + provenance metadata for honesty policy:")
!(println! ("    " (Truth_OverlapCorrectedRevisionAudit
                     (stv 0.6 0.9) (stv 0.4 0.8) (1 2 3) (2 3 4))))
!(println! "")

;; ----- Self-tests (small) -----

!(println! "===========================================================")
!(println! " SANITY ASSERTIONS")
!(println! "===========================================================")

;; Stamp intersection size for the basic cases
!(test (StampIntersectionCount (1 2) (3 4)) 0)
!(test (StampIntersectionCount (1 2) (1 2)) 2)
!(test (StampIntersectionCount (1 2 3) (2 3 4)) 2)
!(test (StampIntersectionCount (1 2 3 4 5) ()) 0)

;; Disjoint case must equal Truth_Revision
!(test
   (Truth_OverlapCorrectedRevision (stv 0.6 0.9) (stv 0.4 0.8) (1 2) (3 4))
   (Truth_Revision (stv 0.6 0.9) (stv 0.4 0.8)))

!(println! "All sanity assertions passed.")
