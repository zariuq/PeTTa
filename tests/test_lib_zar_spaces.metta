;;; test_lib_zar_spaces.metta - Tests for new-space / delete-space from lib_zar
;;; These are gensym-based Prolog workarounds for PeTTa's compiler limitation
;;; (new-space inside function bodies causes =../2 type error)

!(import! &self ../lib/lib_zar)

!(println! "=== Test lib_zar new-space / delete-space ===")
!(println! "")

;;; -------------------------------------------------------
;;; 1. Basic creation: new-space returns a unique atom
;;; -------------------------------------------------------

!(println! "--- Test 1: new-space returns unique atoms ---")

!(let $s1 (new-space)
   (let $s2 (new-space)
     (let $s3 (new-space)
       (if (and (!= $s1 $s2) (and (!= $s2 $s3) (!= $s1 $s3)))
           (println! "PASS: three new-space calls return distinct atoms")
           (progn
             (println! "FAIL: spaces not distinct")
             (println! ($s1 $s2 $s3)))))))

;;; -------------------------------------------------------
;;; 2. add-atom + match on a new-space
;;; -------------------------------------------------------

!(println! "--- Test 2: add-atom + match on new-space ---")

!(let $s (new-space)
   (let* (
     ($_1 (add-atom $s (color red)))
     ($_2 (add-atom $s (color blue)))
     ($results (collapse (match $s (color $c) $c)))
   ) (if (== (size-atom $results) 2)
         (println! "PASS: match retrieves 2 atoms from new space")
         (progn
           (println! "FAIL: expected 2 results")
           (println! $results)))))

;;; -------------------------------------------------------
;;; 3. Isolation: spaces do not leak into each other
;;; -------------------------------------------------------

!(println! "--- Test 3: space isolation ---")

!(let $s1 (new-space)
   (let $s2 (new-space)
     (let* (
       ($_1 (add-atom $s1 (item alpha)))
       ($_2 (add-atom $s2 (item beta)))
       ($r1 (collapse (match $s1 (item $x) $x)))
       ($r2 (collapse (match $s2 (item $x) $x)))
     ) (if (and (== $r1 (alpha)) (== $r2 (beta)))
           (println! "PASS: spaces are isolated")
           (progn
             (println! "FAIL: space leak detected")
             (println! (s1 $r1 s2 $r2)))))))

;;; -------------------------------------------------------
;;; 4. delete-space clears contents
;;; -------------------------------------------------------

!(println! "--- Test 4: delete-space clears space ---")

!(let $s (new-space)
   (let* (
     ($_1 (add-atom $s (data 42)))
     ($before (collapse (match $s (data $x) $x)))
     ($_2 (delete-space $s))
     ($after (collapse (match $s (data $x) $x)))
   ) (if (and (== $before (42)) (== $after ()))
         (println! "PASS: delete-space cleared contents")
         (progn
           (println! "FAIL: delete-space did not clear")
           (println! (before $before after $after))))))

;;; -------------------------------------------------------
;;; 5. delete-space returns true
;;; -------------------------------------------------------

!(println! "--- Test 5: delete-space return value ---")

!(let $s (new-space)
   (let $ret (delete-space $s)
     (if (== $ret true)
         (println! "PASS: delete-space returns true")
         (progn
           (println! "FAIL: unexpected return value")
           (println! $ret)))))

;;; -------------------------------------------------------
;;; 6. new-space inside a function body (the key use case)
;;; -------------------------------------------------------

!(println! "--- Test 6: new-space inside function body ---")

(= (make-and-use-space $val)
   (let $s (new-space)
     (let* (
       ($_1 (add-atom $s (payload $val)))
       ($r (collapse (match $s (payload $x) $x)))
       ($_2 (delete-space $s))
     ) $r)))

!(let $result (make-and-use-space hello)
   (if (== $result (hello))
       (println! "PASS: new-space works inside function body")
       (progn
         (println! "FAIL: function-body new-space broken")
         (println! $result))))

;;; -------------------------------------------------------
;;; 7. Many spaces created and deleted (leak check)
;;; Uses if-guard to prevent overlapping clause non-determinism
;;; -------------------------------------------------------

!(println! "--- Test 7: create and delete 20 spaces ---")

(= (create-delete-loop $n)
   (if (<= $n 0)
       (ok)
       (let $s (new-space)
         (let* (
           ($_1 (add-atom $s (temp $n)))
           ($_2 (delete-space $s))
         ) (create-delete-loop (- $n 1))))))

!(let $result (create-delete-loop 20)
   (if (== $result (ok))
       (println! "PASS: 20 spaces created and deleted without error")
       (progn
         (println! "FAIL: loop did not complete")
         (println! $result))))

;;; -------------------------------------------------------
;;; 8. remove-atom on gensym space
;;; -------------------------------------------------------

!(println! "--- Test 8: remove-atom from gensym space ---")

!(let $s (new-space)
   (let* (
     ($_1 (add-atom $s (keep this)))
     ($_2 (add-atom $s (remove this)))
     ($_3 (remove-atom $s (remove this)))
     ($r (collapse (match $s (keep $x) $x)))
   ) (if (== $r (this))
         (println! "PASS: remove-atom works on gensym space")
         (progn
           (println! "FAIL: remove-atom didn't work")
           (println! $r)))))

;;; -------------------------------------------------------
;;; 9. Double delete (idempotent)
;;; -------------------------------------------------------

!(println! "--- Test 9: double delete-space is safe ---")

!(let $s (new-space)
   (let* (
     ($_1 (add-atom $s (ephemeral data)))
     ($_2 (delete-space $s))
     ($_3 (delete-space $s))
   ) (println! "PASS: double delete-space did not crash")))

;;; -------------------------------------------------------
;;; 10. Reuse after delete: space name freed, new atoms work
;;; -------------------------------------------------------

!(println! "--- Test 10: add to space after delete ---")

!(let $s (new-space)
   (let* (
     ($_1 (add-atom $s (round1 val)))
     ($_2 (delete-space $s))
     ($_3 (add-atom $s (round2 val)))
     ($r (collapse (match $s (round2 $x) $x)))
   ) (if (== $r (val))
         (println! "PASS: space usable after delete + re-add")
         (progn
           (println! "FAIL: could not reuse space")
           (println! $r)))))

;;; -------------------------------------------------------

!(println! "")
!(println! "=== All lib_zar space tests done ===")
