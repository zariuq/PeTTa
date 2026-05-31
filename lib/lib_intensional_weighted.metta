; ============================================================================
; INTENSIONAL WEIGHTED INHERITANCE (§14 Concrete) for PeTTa
; ============================================================================
;
; Operational weighted-property intensional inheritance with provenance-aware
; aggregation for Hyperon/PeTTa.
;
; Key design choices in this revision:
;   - direct property lookup is AUDITED instead of collapsed immediately to a
;     single winner,
;   - packet aggregation uses explicit scratch spaces plus foldl-atom, not
;     recursive car/cdr tuple walking,
;   - packet stamps use a deduplicated union helper instead of shadowing the
;     core StampConcat.
;
; Honest scope note:
;   This is still a runtime-oriented weighted-evidence realization, not an
;   exact mutual-information implementation.
; ============================================================================

!(import! &self lib_he)
!(import! &self lib_pln_query_audit)
!(import! &self lib_overlap_corrected_revision)

!(bind! &intensional_packets (new-space))
!(bind! &intensional_meta (new-space))

(= (Intensional.ClearSpace $space)
   (collapse
     (match $space $atom
            (remove-atom $space $atom))))

(= (Intensional.PacketStampUnion $S1 $S2)
   (Unique (StampConcat $S1 $S2) ()))

(= (Intensional.SourceConceptProps $kb $concept)
   (if (is-space $kb)
       (collapse (match $kb (ConceptProp $concept $P $w) ($P $w)))
       (collapse (match &self (ConceptProp $concept $P $w) ($P $w)))))

(= (PropertyBeliefAudit $kb $entity $prop $maxsteps)
   (if (is-space $kb)
       (collapse
         (match $kb
                (Sentence ((Inheritance $entity (IntSet $prop)) $tv) $stamp)
                ($tv $stamp)))
       (collapse
         (match &self
                (Sentence ((Inheritance $entity (IntSet $prop)) $tv) $stamp)
                ($tv $stamp)))))

(= (PropertyBeliefAudit $kb $entity $prop)
   (PropertyBeliefAudit $kb $entity $prop 0))

(= (PropertyBeliefTopTiesFromAudit $audit)
   (PLN.QueryTopTiesFromAudit $audit))

(= (PropertyBeliefTopTies $kb $entity $prop $maxsteps)
   (PropertyBeliefTopTiesFromAudit
     (PropertyBeliefAudit $kb $entity $prop $maxsteps)))

(= (PropertyBeliefTopTies $kb $entity $prop)
   (PropertyBeliefTopTies $kb $entity $prop 0))

(= (ReweighSTV (stv $s $c) $weight)
   (let* (($w (Truth_c2w $c))
          ($scaled_w (* $w $weight))
          ($scaled_c (Truth_w2c $scaled_w)))
         (stv $s (min 1.0 $scaled_c))))

(= (IntensionalPacket ($tv $stamp) $weight)
   ((ReweighSTV $tv $weight) $stamp))

(= (Intensional.PacketSnapshot)
   (Unique
     (collapse
       (match &intensional_packets
              (packet $prop $tv $stamp)
              ($prop $tv $stamp)))
     ()))

(= (Intensional.CoveredSnapshot)
   (Unique
     (collapse
       (match &intensional_meta (covered $prop) $prop))
     ()))

(= (Intensional.MissingSnapshot)
   (Unique
     (collapse
       (match &intensional_meta (missing $prop) $prop))
     ()))

(= (Intensional.CollectPropertyPackets $kb $entity $maxsteps ($P $w))
   (let $audit (PropertyBeliefAudit $kb $entity $P $maxsteps)
        (if (== $audit ())
            (let $_missing
                 (add-atom &intensional_meta (missing $P))
                 True)
            (let* (($_covered
                     (add-atom &intensional_meta (covered $P)))
                    ($_packets
                     (collapse
                       (let $belief (superpose $audit)
                            (case $belief
                                  ((($tv $stamp)
                                    (let $weighted (eval (ReweighSTV $tv $w))
                                         (add-atom &intensional_packets
                                                   (packet $P $weighted $stamp))))))))))
                  True))))

(= (Intensional.LoadConceptPackets $kb $entity $concept $maxsteps)
   (let* (($props (Intensional.SourceConceptProps $kb $concept))
          ($_clearPackets (Intensional.ClearSpace &intensional_packets))
          ($_clearMeta (Intensional.ClearSpace &intensional_meta))
          ($_collect
            (foldl-atom $props True $acc $pair
              (Intensional.CollectPropertyPackets $kb $entity $maxsteps $pair))))
         True))

(= (Intensional.MergePacketStep ($accTv $accStamp) ($prop $tv $stamp))
   ((Truth_OverlapCorrectedRevision $accTv $tv $accStamp $stamp)
    (Intensional.PacketStampUnion $accStamp $stamp)))

(= (Intensional.ReducePackets ())
   ((stv 0.0 0.0) ()))

(= (Intensional.ReducePackets $packets)
   (foldl-atom $packets ((stv 0.0 0.0) ()) Intensional.MergePacketStep))

(= (PacketTV ($tv $stamp)) $tv)
(= (PacketStamp ($tv $stamp)) $stamp)

(= (ResultTV (intensional-result $tv $stamp (covered $covered) (missing $missing) (blocked $blocked)))
   $tv)
(= (ResultStamp (intensional-result $tv $stamp (covered $covered) (missing $missing) (blocked $blocked)))
   $stamp)
(= (ResultCovered (intensional-result $tv $stamp (covered $covered) (missing $missing) (blocked $blocked)))
   $covered)
(= (ResultMissing (intensional-result $tv $stamp (covered $covered) (missing $missing) (blocked $blocked)))
   $missing)
(= (ResultBlocked (intensional-result $tv $stamp (covered $covered) (missing $missing) (blocked $blocked)))
   $blocked)

(= (IntensionalMemberSTV $kb $entity $concept $maxsteps)
   (let* (($_load (Intensional.LoadConceptPackets $kb $entity $concept $maxsteps))
          ($folded (Intensional.ReducePackets (Intensional.PacketSnapshot))))
         (PacketTV $folded)))

(= (IntensionalMemberSTV $kb $entity $concept)
   (IntensionalMemberSTV $kb $entity $concept 0))

(= (IntensionalMemberAudit $kb $entity $concept $maxsteps)
   (let* (($_load (Intensional.LoadConceptPackets $kb $entity $concept $maxsteps))
          ($folded (Intensional.ReducePackets (Intensional.PacketSnapshot))))
         (intensional-result
            (PacketTV $folded)
            (PacketStamp $folded)
            (covered (Intensional.CoveredSnapshot))
            (missing (Intensional.MissingSnapshot))
            (blocked ()))))

(= (IntensionalMemberAudit $kb $entity $concept)
   (IntensionalMemberAudit $kb $entity $concept 0))
