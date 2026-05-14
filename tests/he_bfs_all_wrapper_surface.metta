!(bind! &dupunseed (new-space))
!(import! &self ./support/tilepuzzle_move9_defs.metta)
!(import! &self ../lib/lib_datastructures.metta)

(= (bfs_loop_limited_unseeded (empty-queue) $N0 $limit) $N0)
(= (bfs_loop_limited_unseeded $Q $N0 $limit)
   (if (>= $N0 $limit)
       $N0
       (let* (($Q1 (once (dequeue $S $Q)))
              ($Ln (collapse
                     (let* (($Snew (move $S $_))
                            ($2 (add-unique-or-fail &dupunseed $Snew)))
                           $Snew)))
              ($Q2 (foldl enqueue $Ln $Q1))
              ($N1 (+ $N0 1)))
         (bfs_loop_limited_unseeded $Q2 $N1 $limit))))

(= (bfs_all_unseeded_limited $Start $limit)
   (let* (($seed (add-unique-item-or-empty $Start))
          ($Q1 (enqueue $Start (empty-queue))))
     (bfs_loop_limited_unseeded $Q1 0 $limit)))

!(assertEqual (let $_ (bfs_all_unseeded_limited (___ 1 2 3 4 5 6 7 8) 1)
                    (count-atoms &dupunseed))
               2)
