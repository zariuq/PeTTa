!(add-atom &self (: ⟨0⟩ Const))
!(add-atom &self (: ⟨+⟩ Const))
!(add-atom &self (: ⟨=⟩ Const))
!(add-atom &self (: ⟨->⟩ Const))
!(add-atom &self (: ⟨⟦⟩ Const))
!(add-atom &self (: ⟨⟧⟩ Const))
!(add-atom &self (: ⟨term⟩ Const))
!(add-atom &self (: ⟨wff⟩ Const))
!(add-atom &self (: ⟨|-⟩ Const))
!(add-atom &self (: ⟨t⟩ Var))
!(add-atom &self (: ⟨r⟩ Var))
!(add-atom &self (: ⟨s⟩ Var))
!(add-atom &self (: ⟨P⟩ Var))
!(add-atom &self (: ⟨Q⟩ Var))
!(add-atom &self (: tt (: ⟨t⟩ ⟨term⟩)))
!(add-atom &self (: tr (: ⟨r⟩ ⟨term⟩)))
!(add-atom &self (: ts (: ⟨s⟩ ⟨term⟩)))
!(add-atom &self (: wp (: ⟨P⟩ ⟨wff⟩)))
!(add-atom &self (: wq (: ⟨Q⟩ ⟨wff⟩)))
!(add-atom &self (: tze (: ⟨0⟩ ⟨term⟩)))
!(add-atom &self (: tpl (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨+⟩ $⟨r⟩ ) ⟨term⟩))))
!(add-atom &self (: weq (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨r⟩) ⟨wff⟩))))
!(add-atom &self (: wim (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨wff⟩))))
!(add-atom &self (: a1 (-> (: $⟨t⟩ ⟨term⟩) (: $⟨r⟩ ⟨term⟩) (: $⟨s⟩ ⟨term⟩) (: ( $⟨t⟩ ⟨=⟩ $⟨r⟩ ⟨->⟩ ( $⟨t⟩ ⟨=⟩ $⟨s⟩ ⟨->⟩ $⟨r⟩ ⟨=⟩ $⟨s⟩ ) ) ⟨|-⟩))))
!(add-atom &self (: a2 (-> (: $⟨t⟩ ⟨term⟩) (: (( $⟨t⟩ ⟨+⟩ ⟨0⟩ ) ⟨=⟩ $⟨t⟩) ⟨|-⟩))))
!(add-atom &self (: mp (-> (: $⟨P⟩ ⟨wff⟩) (: $⟨Q⟩ ⟨wff⟩) (: $⟨P⟩ ⟨|-⟩) (: ( $⟨P⟩ ⟨->⟩ $⟨Q⟩ ) ⟨|-⟩) (: $⟨Q⟩ ⟨|-⟩))))
; !(add-atom &md (: th1 (-> (: $⟨t⟩ ⟨term⟩) (: ($⟨t⟩ ⟨=⟩ $⟨t⟩) ⟨|-⟩))))

;; Curried versions are needed.
!(add-atom &self (: mp-curry
  (-> (: $P ⟨wff⟩)                    ; P is a wff
    (-> (: $Q ⟨wff⟩)                  ; Q is a wff  
      (-> (: $P ⟨|-⟩)                 ; P is provable
        (-> (: ($P ⟨->⟩ $Q) ⟨|-⟩)     ; (P -> Q) is provable
          (: $Q ⟨|-⟩)))))))           ; conclusion: Q is provable

!(add-atom &self (: a1-curry 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: ($t ⟨=⟩ $r ⟨->⟩ ($t ⟨=⟩ $s ⟨->⟩ $r ⟨=⟩ $s)) ⟨|-⟩))))))

!(add-atom &self (: a1-curry' 
  (-> (: $t ⟨term⟩)
    (-> (: $r ⟨term⟩) 
      (-> (: $s ⟨term⟩)
        (: (($t ⟨=⟩ $r) ⟨->⟩ (($t ⟨=⟩ $s) ⟨->⟩ ($r ⟨=⟩ $s))) ⟨|-⟩))))))

;; The result of demo0.mm can be constructed.
!(include metamath)
; > !(get-type (((a1-curry (tpl tt tze)) tt) tt))
; [(: ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩ ⟨->⟩ ((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩ ⟨->⟩ ⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)]
; > !(get-type (((a1-curry' (tpl tt tze)) tt) tt))
; [(: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩))) ⟨|-⟩)]
; > !(get-type ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt)))
; [(: (((⟨t⟩ ⟨+⟩ ⟨0⟩) ⟨=⟩ ⟨t⟩) ⟨->⟩ (⟨t⟩ ⟨=⟩ ⟨t⟩)) ⟨|-⟩)]
; > !(get-type ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))))
; [(: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)]

!(bc &self
   Nil
   (fromNumber 10)                   
   (: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))
; [(: ((((mp-curry (weq (tpl tt tze) tt)) (weq tt tt)) (a2 tt)) ((((mp-curry (weq (tpl tt tze) tt)) (wim (weq (tpl tt tze) tt) (weq tt tt))) (a2 tt)) (((a1-curry' (tpl tt tze)) tt) tt))) (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩))]

; Not sure how long this will take to run.  There's no guidance.
; !(bc &self
;    Nil
;    (fromNumber 10)                   
;    (: $proof (: (⟨t⟩ ⟨=⟩ ⟨t⟩) ⟨|-⟩)))