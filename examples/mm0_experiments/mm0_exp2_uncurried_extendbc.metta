!(include metamath)

;; Add multi-arity env-bc clauses locally (3- and 4-ary)
;; Ternary
(= (bc $kb $env (S $k) (: ($rule $a1 $a2 $a3) $th))
   (let* (
          ((: $rule (-> $p1 $p2 $p3 $th))
           (bc $kb $env $k (: $rule (-> $p1 $p2 $p3 $th))))
          ((: $a1 $p1) (bc $kb $env $k (: $a1 $p1)))
          ((: $a2 $p2) (bc $kb $env $k (: $a2 $p2)))
          ((: $a3 $p3) (bc $kb $env $k (: $a3 $p3))))
     (: ($rule $a1 $a2 $a3) $th)))

;; Quaternary
(= (bc $kb $env (S $k) (: ($rule $a1 $a2 $a3 $a4) $th))
   (let* (
          ((: $rule (-> $p1 $p2 $p3 $p4 $th))
           (bc $kb $env $k (: $rule (-> $p1 $p2 $p3 $p4 $th))))
          ((: $a1 $p1) (bc $kb $env $k (: $a1 $p1)))
          ((: $a2 $p2) (bc $kb $env $k (: $a2 $p2)))
          ((: $a3 $p3) (bc $kb $env $k (: $a3 $p3)))
          ((: $a4 $p4) (bc $kb $env $k (: $a4 $p4))))
     (: ($rule $a1 $a2 $a3 $a4) $th)))

;; MM0-style sorts and constructors
!(add-atom &self (: term Const))
!(add-atom &self (: wff  Const))
!(add-atom &self (: tt   term))
!(add-atom &self (: tze  term))
!(add-atom &self (: tpl  (-> (: $t term) (: $r term) term)))
!(add-atom &self (: weq  (-> (: $t term) (: $r term) wff)))
!(add-atom &self (: wim  (-> (: $P wff) (: $Q wff) wff)))

;; Helpful typed wff atoms to satisfy base matches
!(add-atom &self (: (weq (tpl tt tze) tt) wff))
!(add-atom &self (: (weq tt tt) wff))
!(add-atom &self (: (wim (weq (tpl tt tze) tt) (weq tt tt)) wff))

;; Uncurried rules (as in mm0 demo0.mmu)
!(add-atom &self (: a1 (-> (: $t term)
                           (: $r term)
                           (: $s term)
                           (wim (weq $t $r)
                                (wim (weq $t $s)
                                     (weq $r $s))))))
!(add-atom &self (: a2 (-> (: $t term)
                           (weq (tpl $t tze) $t))))
!(add-atom &self (: mp (-> (: $maj (wim $P $Q))
                           (: $P wff)
                           (: $Q wff)
                           (: $min $P)
                           $Q)))

;; Print one derived proof
!(println!
  (repr
    (collapse
      (bc &self Nil (fromNumber 5)
          (: $p (weq tt tt))))))
