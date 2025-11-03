;; FINAL SOLUTION: Cross-Platform string< for both HE and PeTTa
;;
;; This provides lexicographic string comparison that works in BOTH systems:
;; - In HE: Uses py-dot to call Python's __lt__ method
;; - In PeTTa: Uses @< (Prolog's lexicographic comparison operator)

(: string< (-> Expression Expression Bool))
(= (string< $x $y)
  (case ((py-dot $x __lt__) $y)
    ((true true)                        ; HE: py-dot succeeded, return true
     (false false)                       ; HE: py-dot succeeded, return false
     ((py-dot $_ __lt__) (@< $x $y))   ; PeTTa: py-dot unevaluated, use @<
     ($_ (@< $x $y)))))                ; Fallback: use @<

;; Usage:
;; !(string< "apple" "banana")  ; → true in both HE and PeTTa
;; !(string< "z" "a")           ; → false in both HE and PeTTa
;; !(string< (repr x) (repr y)) ; → Works with repr output too

;; This is what mmverify needs for orient_pair:
;; (= (orient_pair $x $y)
;;    (let ($str_x $str_y) ((repr $x) (repr $y))
;;      (if (string< $str_x $str_y)
;;          ($x $y)
;;          ($y $x))))
