!(include metamath)

;; Minimal MM0-inspired KB in MeTTa terms
;; Sorts: term, wff
!(add-atom &self (: tt term))

;; Constructors
!(add-atom &self (: tze term))
!(add-atom &self (: tpl (-> (: $t term) (: $r term) term)))
!(add-atom &self (: weq (-> (: $t term) (: $r term) wff)))
!(add-atom &self (: wim (-> (: $P wff) (: $Q wff) wff)))

;; Axioms
!(add-atom &self (: a1 (-> (: $t term)
                           (: $r term)
                           (: $s term)
                           (wim (weq $t $r)
                                (wim (weq $t $s)
                                     (weq $r $s))))))

!(add-atom &self (: a2 (-> (: $t term)
                           (weq (tpl $t tze) $t))))

;; Modus Ponens (major premise first)
!(add-atom &self (: mp (-> (: $maj (wim $P $Q))
                           (: $P wff)
                           (: $Q wff)
                           (: $min $P)
                           $Q)))

;; Goal: prove reflexivity (weq tt tt)
!(test
  (bc &self Nil (fromNumber 5)
      (: $prf (weq tt tt)))
  (: (mp (a1 (tpl tt tze) tt tt)
         (weq (tpl tt tze) tt)
         (wim (weq (tpl tt tze) tt) (weq tt tt))
         (a2 tt))
     (weq tt tt)))

!(println! (collapse (bc &self Nil (fromNumber 5) (: $p (weq tt tt)))))
