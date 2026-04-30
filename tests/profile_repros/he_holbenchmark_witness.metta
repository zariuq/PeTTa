; Reduced HE witness for the higher-order benchmark suite.
; This preserves the same recursive map/fold/apply/poly shapes while
; shrinking the workloads enough to certify semantics separately from scale.

(= (count-demo $expr)
   (let $tuple (eval $expr)
        (size-atom $tuple)))

(= (map-flat $f ()) ())
(= (map-flat $f (cons $x $xs)) (cons ($f $x) (map-flat $f $xs)))

(= (range $n)
   (if (== $n 0) ()
       (cons $n (range (- $n 1)))))

!(test (let $temp (map-flat (+ 1) (range 5000))
          (count-demo $temp))
       5000)

(= (fold-nested $f $init ()) $init)
(= (fold-nested $f $init (cons $x $xs))
   (if (is-expr $x)
       (fold-nested $f (fold-nested $f $init $x) $xs)
       (fold-nested $f ($f $init $x) $xs)))

(= (deep-nest $n)
   (if (== $n 0) ()
       (cons (range 50) (deep-nest (- $n 1)))))

!(test (fold-nested + 0 (deep-nest 200))
       255000)

(= (apply-many $f $n $x)
   (if (== $n 0) $x
       (apply-many $f (- $n 1) ($f $x))))

!(test (apply-many (+ 1) 5000 0)
       5000)

(= (poly $f $n)
   (if (== $n 0) 0
       (+ ($f $n) (poly $f (- $n 1)))))

!(test (poly (+ 1) 5000)
       12507500)
