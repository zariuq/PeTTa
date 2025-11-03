;; Cross-platform string comparison for HE and PeTTa
;;
;; This provides string< that works in both implementations:
;; - In HE: Uses py-dot for Python's __lt__ method
;; - In PeTTa: Uses Prolog's string comparison (to be added by Patrick)

;; Attempt 1: Runtime detection approach
;; Try py-dot first, if it fails, try alternative
(= (string<-runtime $x $y)
  (case ((py-dot $x __lt__) $y)
    ((true true)
     (false false)
     ;; If py-dot didn't work, we're in PeTTa - need Patrick's implementation
     ($unevaluated false))))  ; Placeholder - Patrick needs to add this

;; Attempt 2: Conditional compilation approach
;; Define both versions, the working one will be used
(= (string<-he $x $y)
   ((py-dot $x __lt__) $y))

;; This is what Patrick needs to add to PeTTa's metta.pl:
;; 'string<-petta'(A, B, R) :- (A @< B -> R = true ; R = false).

;; Then we can do:
;; (= (string< $x $y)
;;   (string<-petta $x $y))  ; In PeTTa
;; OR
;; (= (string< $x $y)
;;   (string<-he $x $y))  ; In HE

;; Attempt 3: WORKAROUND - Compare symbols character by character
;; This is slow but works everywhere
(= (string-codes $str $codes)
  (case (get-metatype $str)
    ((Symbol (symbol-codes $str))
     (String (string-codes-builtin $str))
     ($_ ()))))

(= (codes< () ()) false)
(= (codes< () $_) true)
(= (codes< $_ ()) false)
(= (codes< (Cons $h1 $t1) (Cons $h2 $t2))
  (if (< $h1 $h2)
      true
      (if (< $h2 $h1)
          false
          (codes< $t1 $t2))))

(= (string<-workaround $x $y)
  (let $cx (repr-to-codes $x)
    (let $cy (repr-to-codes $y)
      (codes< $cx $cy))))

;; Helper to convert repr output to char codes
(= (repr-to-codes $x)
  (let $str (repr $x)
    (atom-codes $str)))  ; If atom-codes exists

;; RECOMMENDED SOLUTION:
;; Have Patrick add this to PeTTa's metta.pl builtin predicates:
;;
;; 'str-lt'(A, B, R) :-
;;     (atom(A), atom(B) ->
;;         atom_string(A, AS),
;;         atom_string(B, BS),
;;         (AS @< BS -> R = true ; R = false)
;;     ;   string(A), string(B) ->
;;         (A @< B -> R = true ; R = false)
;;     ;   R = false
;;     ).
;;
;; Then in MeTTa we can do:
;; (= (string< $x $y) (str-lt $x $y))  ; Works in PeTTa
;; OR keep:
;; (= (string< $x $y) ((py-dot $x __lt__) $y))  ; Works in HE
