!(import! &m f1_moduleA)
(: contains (-> Expression (-> Atom Bool) Bool))
(= (contains $list $condition)
  (if (== $list ()) False
    (let $head (car-atom $list)
      (if ($condition $head) True
        (let $tail (cdr-atom $list) (contains $tail $condition)) ))))
(: is-space (-> Atom Bool))
(= (is-space $atom)
   (let* (($type (get-type $atom)) ($space (get-type &self))) (== $type $space)))
!(let $x (collapse (get-atoms &m)) (get-type $x))
!(let $x (collapse (get-atoms &m)) (get-metatype $x))
!(let $x (collapse (get-atoms &m)) (get-type is-space))
!(let $x (collapse (get-atoms &m)) (get-type contains))
