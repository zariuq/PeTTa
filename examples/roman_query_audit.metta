; ============================================================================
; ROMAN QUERY AUDIT --- audit, top ties, and lightweight pruning
; ============================================================================
;
; PeTTa mirror of the CeTTa query-surface experiment.
; Keeps policy explicit:
;   - QueryAudit      returns all matching candidates,
;   - QueryTopTies    returns all top-confidence ties,
;   - QueryPrunedAudit drops only weaker same-strength candidates.
;
; Important runtime note:
;   These counts are NOT budget-portable to CeTTa. PeTTa reaches a deeper
;   audit frontier under the same numeric maxsteps on this benchmark.
; ============================================================================

!(import! &self ../lib/lib_pln_query_audit)
!(import! &self ../lib/lib_he)

(= (STV A) (stv 0.5 0.9))
(= (STV B) (stv 0.25 0.9))
(= (STV C) (stv 0.25 0.9))
(= (STV D) (stv 0.5 0.9))

(= (kb)
   ((Sentence ((Inheritance A B) (stv 0.25 0.9)) (1))
    (Sentence ((Inheritance B D) (stv 0.5  0.9)) (2))
    (Sentence ((Inheritance A C) (stv 0.25 0.9)) (3))
    (Sentence ((Inheritance C D) (stv 0.5  0.9)) (4))))

(= (audit15)
   (PLN.QueryAudit (kb) (Inheritance A D) 15))

(= (top15)
   (PLN.QueryTopTiesFromAudit (audit15)))

(= (audit25)
   (PLN.QueryAudit (kb) (Inheritance A D) 25))

(= (pruned25)
   (PLN.QueryPrunedAuditFromAudit (audit25)))

!(println! ("audit15" (audit15)))
!(println! ("audit15-count" (TupleCount (audit15))))
!(println! ("top15" (top15)))
!(println! ("top15-count" (TupleCount (top15))))
!(println! ("audit25" (audit25)))
!(println! ("audit25-count" (TupleCount (audit25))))
!(println! ("pruned25" (pruned25)))
!(println! ("pruned25-count" (TupleCount (pruned25))))
!(println! "PeTTa Roman query audit report complete.")
