; %%%% Hyperon-Experimental compatibility library. %%%%
; Many of the included functions were considered ad hoc and
; straightforward to express directly in MeTTa itself:

;Equality and Reduction
(= (if-equal $A $B $Then $Else)
   (if (== $A $B) $Then $Else))

(= (if-equal2 $A $B $Then $Else)
   (if (== $A $B) $Then $Else))

(= (assertEqual $A $B)
   (assert (== $A $B)))

(= (assertAlphaEqual $A $B)
   (assert (=alpha $A $B)))

; unify: Pattern matching in space - if $pattern matches something in $space, return $then, else $else
; This is the HE builtin behavior, implemented using match/collapse for cross-platform compatibility
; Note: This is different from equality testing - it searches for a pattern in a space
;; Original with case - causes non-determinism in PeTTa
;; (: unify (-> SpaceType Atom Expression Expression %Undefined%))
;; (= (unify $space $pattern $then $else)
;;   (let $results (collapse (match $space $pattern $pattern))
;;     (case $results
;;       ((Empty $else)
;;        (() $else)
;;        ($_ $then)))))

;; Fixed version using if - deterministic
(= (unify $space $pattern $then $else)
  (let $results (collapse (match $space $pattern $pattern))
    (if (== $results ())
        $else
        $then)))

(: add-reduct (-> %Undefined% Expression Bool))
(= (add-reduct $space $f)
   (let* (($headbody (cdr-atom $f))
          ($head (car-atom $headbody))
          ($body (cdr-atom $headbody))
          ($bodyreduced (eval $body)))
         (add-atom $space (= $head $bodyreduced))))

;Error Handling
(= (if-error $X $A $B)
   (if (== (car-atom $X) Error) 
       $A $B))

(= (return-on-error $result $B)
   (if-error $result
             $result
             $B))

;Evaluation control
(= (for-each-in-atom $L $f)
   (map-atom $L $f))

(: evalc (-> Expression %Undefined% %Undefined%))
(= (evalc $expression &self)
   (eval $expression))

;Quoting
(: unquote (-> Expression %Undefined%))
(= (unquote (quote $A))
   (eval $A))

(: noreduce-eq (-> Expression Expression Bool))
(= (noreduce-eq $A $B)
   (== $A $B))

;Types
(= (is-function (-> $A $B)) (let $temp (cut) True))
(= (is-function $X) False)

(= (get-type-space &self $x)
   (get-type $x))

(= (match-types $A $B $Then $Else)
   (if (== $A $B) $Then $Else))

(= (match-type-or $value $type1 $type2)
   (match-types $type1 $type2 True $value))
