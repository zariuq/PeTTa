; ============================================================================
; INTENSIONAL WEIGHTED AMBIGUITY --- audit and top ties for trait evidence
; ============================================================================
;
; PeTTa report companion for ambiguous evidence inside a weighted trait.
; This keeps the implementation untouched and makes the nested audit values
; visible at the example layer.
; ============================================================================

!(import! &self ../lib/lib_he)
!(import! &self ../lib/lib_pln)
!(import! &self ../lib/lib_overlap_corrected_revision)
!(import! &self ../lib/lib_intensional_weighted)

!(bind! &kb (new-space))

!(add-atom &kb (ConceptProp reliable-lite shows-up-on-time 1.0))
!(add-atom &kb (ConceptProp reliable-lite returns-messages 0.5))

!(add-atom &kb (Sentence ((Inheritance casey (IntSet shows-up-on-time)) (stv 0.8 0.9)) (501)))
!(add-atom &kb (Sentence ((Inheritance casey (IntSet shows-up-on-time)) (stv 0.3 0.9)) (502)))
!(add-atom &kb (Sentence ((Inheritance casey (IntSet returns-messages)) (stv 0.7 0.8)) (503)))

(= (shows-up-audit)
   (PropertyBeliefAudit &kb casey shows-up-on-time 30))

(= (shows-up-top)
   (PropertyBeliefTopTies &kb casey shows-up-on-time 30))

(= (casey-reliable-audit)
   (IntensionalMemberAudit &kb casey reliable-lite 30))

!(test (TupleCount (shows-up-audit)) 2)
!(test (TupleCount (shows-up-top)) 2)

!(println! "==========================================================")
!(println! "INTENSIONAL WEIGHTED AMBIGUITY --- Casey / reliable-lite")
!(println! "==========================================================")
!(println! ("shows-up-audit" (shows-up-audit)))
!(println! ("shows-up-audit-count" (TupleCount (shows-up-audit))))
!(println! ("shows-up-top" (shows-up-top)))
!(println! ("shows-up-top-count" (TupleCount (shows-up-top))))
!(println! ("casey-reliable-audit" (casey-reliable-audit)))
!(println! "PeTTa intensional ambiguity checks passed.")
