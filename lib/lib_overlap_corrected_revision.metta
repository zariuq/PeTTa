; ============================================================================
; OVERLAP-CORRECTED REVISION (Level 1) for PeTTa PLN
; ============================================================================
;
; PeTTa's lib_pln currently provides two stamp operations:
;   - StampDisjoint $S1 $S2 -- boolean: is the intersection empty?
;   - StampConcat   $S1 $S2 -- sorted union
;
; And the additive revision:
;   - Truth_Revision (stv s1 c1) (stv s2 c2) -- additive weighted-average
;
; The binary StampDisjoint gate is Level 0: it BLOCKS merging when any
; provenance is shared.  This is conservative but loses information ---
; partially-overlapping evidence sources still carry SOME independent
; signal that we'd like to credit.
;
; This module adds the Level 1 graded overlap-correction.  The formula is
; an operational adaptation of:
;
;   Mettapedia/Logic/AbstractInheritanceOverlap.lean:140
;     overlapEvidence x y := (x.stamp ∩ y.stamp).sum stampContribution
;
;   Mettapedia/Logic/WorldModelOverlap.lean:113
;     SubtractiveOverlapLayer.inclusionExclusion
;       extract (merge W1 W2) q = extract W1 q + extract W2 q - overlap W1 W2 q
;
; PeTTa stamps are unlabelled integer tuples (no posExt/negInt distinction)
; so we adapt the formula under the assumption that each stamp element
; represents one observation contributing uniformly to its belief's evidence:
;
;   per_pos_i = pos_i / |S_i|          (per-observation positive contribution)
;   per_neg_i = neg_i / |S_i|          (per-observation negative contribution)
;
;   overlap_pos = |S1 ∩ S2| * (per_pos_1 + per_pos_2) / 2
;   overlap_neg = |S1 ∩ S2| * (per_neg_1 + per_neg_2) / 2
;
;   merged_pos  = (pos1 + pos2) - overlap_pos           (inclusion-exclusion)
;   merged_neg  = (neg1 + neg2) - overlap_neg
;
; Sanity:
;   |S1 ∩ S2| = 0       -->  additive revision (Level 0 disjoint case)
;   S1 = S2 = stamp S   -->  merged = (pos1+pos2)/2, (neg1+neg2)/2  (average)
;   Partial overlap     -->  linearly interpolated between the two
;
; Honesty caveat:
;   This is the operational Level 1 adaptation, NOT a closed-form proof from
;   the Lean side.  The Lean theorem (correctedMerge_eq_revise_of_stampDisjoint)
;   covers the disjoint endpoint exactly.  The graded interpolation is the
;   defensible heuristic; tightening it to a theorem would require enriching
;   stamps with per-element evidence labels (cf. AbstractInheritanceOverlap.lean
;   stampContribution definition with WitnessStamp variants).
;
; ============================================================================

;; Stamp intersection: elements appearing in both tuples.
;; Returns a tuple of matching elements (length = |S1 ∩ S2|).
(= (StampIntersection $S1 $S2)
   (collapse (let* (($x (superpose $S1))
                    ($y (superpose $S2)))
                   (case (== $x $y) ((True $x))))))

;; Stamp intersection size: count of matching elements.
(= (StampIntersectionCount $S1 $S2)
   (TupleCount (StampIntersection $S1 $S2)))

;; Per-stamp-element pos and neg evidence contribution from a sentence's TV.
;; pos = strength * weight, neg = (1-strength) * weight, weight = c/(1-c).
;; Divided by stamp size for the per-observation contribution.
(= (PerStampPos $s $c $stampSize)
   (if (> $stampSize 0)
       (let* (($w (Truth_c2w $c))
              ($pos (* $s $w)))
             (/ $pos $stampSize))
       0))

(= (PerStampNeg $s $c $stampSize)
   (if (> $stampSize 0)
       (let* (($w (Truth_c2w $c))
              ($neg (* (- 1 $s) $w)))
             (/ $neg $stampSize))
       0))

;; The operational overlap-corrected revision.
;;
;; Two-stamp Level 1 graded merge:
;;   merge of (stv s1 c1, stamp S1) and (stv s2 c2, stamp S2) is corrected by
;;   subtracting the shared-stamp evidence (using stamp-intersection count
;;   weighted by averaged per-stamp contribution).
;;
;; Returns the merged (stv strength confidence).  When the stamps are
;; disjoint, this reduces to Truth_Revision exactly.
(= (Truth_OverlapCorrectedRevision (stv $s1 $c1) (stv $s2 $c2) $S1 $S2)
   (let* (($w1 (Truth_c2w $c1))
          ($w2 (Truth_c2w $c2))
          ($pos1 (* $s1 $w1))
          ($neg1 (* (- 1 $s1) $w1))
          ($pos2 (* $s2 $w2))
          ($neg2 (* (- 1 $s2) $w2))
          ($size1 (TupleCount $S1))
          ($size2 (TupleCount $S2))
          ($shared (StampIntersectionCount $S1 $S2))
          ($per_pos_1 (PerStampPos $s1 $c1 $size1))
          ($per_pos_2 (PerStampPos $s2 $c2 $size2))
          ($per_neg_1 (PerStampNeg $s1 $c1 $size1))
          ($per_neg_2 (PerStampNeg $s2 $c2 $size2))
          ($shared_pos (* $shared (/ (+ $per_pos_1 $per_pos_2) 2)))
          ($shared_neg (* $shared (/ (+ $per_neg_1 $per_neg_2) 2)))
          ($naive_pos (+ $pos1 $pos2))
          ($naive_neg (+ $neg1 $neg2))
          ($merged_pos (if (> $naive_pos $shared_pos) (- $naive_pos $shared_pos) 0))
          ($merged_neg (if (> $naive_neg $shared_neg) (- $naive_neg $shared_neg) 0))
          ($merged_total (+ $merged_pos $merged_neg))
          ($merged_s (if (> $merged_total 0) (/ $merged_pos $merged_total) 0))
          ($merged_c (Truth_w2c $merged_total)))
         (stv (min 1.0 $merged_s) (min 1.0 $merged_c))))

;; Optional: return the diagnostic overlap-count alongside the merged TV.
;; Useful for honesty/abstention policies that want to know how much
;; provenance overlap was discounted.
(= (Truth_OverlapCorrectedRevisionAudit (stv $s1 $c1) (stv $s2 $c2) $S1 $S2)
   (let* (($merged (Truth_OverlapCorrectedRevision (stv $s1 $c1) (stv $s2 $c2) $S1 $S2))
          ($shared (StampIntersectionCount $S1 $S2))
          ($size1 (TupleCount $S1))
          ($size2 (TupleCount $S2)))
         (overlap-corrected
            (merged $merged)
            (stamp1-size $size1)
            (stamp2-size $size2)
            (shared $shared)
            (stamp1 $S1)
            (stamp2 $S2)
            (stamp-union (StampConcat $S1 $S2)))))
