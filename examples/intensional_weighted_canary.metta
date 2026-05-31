; ============================================================================
; INTENSIONAL WEIGHTED CANARY --- singleton, missing, overlap
; ============================================================================

!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln)
!(import! &self ../lib/lib_overlap_corrected_revision)
!(import! &self ../lib/lib_intensional_weighted)

!(bind! &kb (new-space))

!(add-atom &kb (ConceptProp punctual shows-up-on-time 1.0))
!(add-atom &kb (ConceptProp careful-lite double-checks-work 1.0))
!(add-atom &kb (ConceptProp careful-lite asks-for-clarification 0.5))
!(add-atom &kb (ConceptProp consistent p1 1.0))
!(add-atom &kb (ConceptProp consistent p2 1.0))

!(add-atom &kb (Sentence ((Inheritance alice (IntSet shows-up-on-time)) (stv 0.8 0.9)) (101)))
!(add-atom &kb (Sentence ((Inheritance bob (IntSet double-checks-work)) (stv 0.6 0.8)) (401)))
!(add-atom &kb (Sentence ((Inheritance dana-disjoint (IntSet p1)) (stv 0.7 0.9)) (201)))
!(add-atom &kb (Sentence ((Inheritance dana-disjoint (IntSet p2)) (stv 0.7 0.9)) (202)))
!(add-atom &kb (Sentence ((Inheritance dana-overlap (IntSet p1)) (stv 0.7 0.9)) (301)))
!(add-atom &kb (Sentence ((Inheritance dana-overlap (IntSet p2)) (stv 0.7 0.9)) (301)))

(= (singleton-stv)
   (IntensionalMemberSTV &kb alice punctual 30))

(= (missing-audit)
   (IntensionalMemberAudit &kb bob careful-lite 30))

(= (disjoint-stv)
   (IntensionalMemberSTV &kb dana-disjoint consistent 30))

(= (overlap-stv)
   (IntensionalMemberSTV &kb dana-overlap consistent 30))

!(test (singleton-stv)
       (stv 0.8 0.9))

!(test (missing-audit)
       (intensional-result
         (stv 0.6 0.8)
         (401)
         (covered (double-checks-work))
         (missing (asks-for-clarification))
         (blocked ())))

!(test (disjoint-stv)
       (stv 0.7 0.9473684210526316))

!(test (overlap-stv)
       (stv 0.7 0.9))

!(println! "PeTTa intensional weighted canary checks passed.")
