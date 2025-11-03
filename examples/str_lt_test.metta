;; str-lt test for HE 0.2.8 (no PeTTa runtime)
;; Define str-lt in pure MeTTa using repr + Python string __lt__

(: str-lt (-> $x $y Bool))
(= (str-lt $x $y)
   ((py-dot (repr $x) __lt__) (repr $y)))

;; Basic sanity checks
!(println! (str-lt "a" "b"))          ; expect true
!(println! (str-lt "aa" "ab"))        ; expect true
!(println! (str-lt "b" "a"))          ; expect false

;; Non-strings via repr
!(println! (str-lt (Cons A Nil) (Cons B Nil)))   ; expect true if "A" < "B"
!(println! (str-lt (Cons Z Nil) (Cons Y Nil)))   ; expect false if "Z" > "Y"

