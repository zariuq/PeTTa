(= (bad) (progn (println! "BAD-RHS-MUST-NOT-RUN") "bad"))
!(test (and-then False (bad)) False)
!(test (or-else True (bad)) True)
