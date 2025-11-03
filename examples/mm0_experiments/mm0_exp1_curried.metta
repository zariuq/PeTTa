!(include metamath)

;; MM0-style sorts and constructors (minimal)
!(add-atom &self (: term Const))
!(add-atom &self (: wff  Const))
!(add-atom &self (: tt   term))
!(add-atom &self (: tze  term))
!(add-atom &self (: tpl  (-> (: $t term) (: $r term) term)))
!(add-atom &self (: weq  (-> (: $t term) (: $r term) wff)))
!(add-atom &self (: wim  (-> (: $P wff) (: $Q wff) wff)))
!(add-atom &self (: a2   (-> (: $t term) (weq (tpl $t tze) $t))))

;; Curried versions so the existing env-bc (unary/binary) can chain
!(add-atom &self (: a1-curry
  (-> (: $t term)
    (-> (: $r term)
      (-> (: $s term)
        (wim (weq $t $r)
             (wim (weq $t $s)
                  (weq $r $s))))))))

!(add-atom &self (: mp-curry
  (-> (: $P wff)
    (-> (: $Q wff)
      (-> (: $P wff)
        (-> (wim $P $Q)
            $Q))))))

;; Sanity: can we derive (weq (tpl tt tze) tt) via a2?
!(println! (repr (collapse (bc &self Nil (fromNumber 2) (: $p (weq (tpl tt tze) tt))))))

;; Target: derive (weq tt tt) using a1-curry + mp-curry + a2
!(println! (repr (collapse (bc &self Nil (fromNumber 6) (: $p (weq tt tt))))))
