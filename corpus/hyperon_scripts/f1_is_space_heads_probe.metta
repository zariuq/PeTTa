!(import! &m f1_moduleA)
!(let $x (collapse (get-atoms &m)) (car-atom $x))
!(let $x (collapse (get-atoms &m)) (is-space (car-atom $x)))
!(let $x (collapse (get-atoms &m)) (cdr-atom $x))
!(let $x (collapse (get-atoms &m)) (contains $x is-space))
(: contains (-> Expression (-> Atom Bool) Bool))
(= (contains $list $condition)
  (if (== $list ()) False
    (let $head (car-atom $list)
      (if ($condition $head) True
        (let $tail (cdr-atom $list) (contains $tail $condition)) ))))
(: is-space (-> Atom Bool))
(= (is-space $atom)
   (let* (($type (get-type $atom)) ($space (get-type &self))) (== $type $space)))
