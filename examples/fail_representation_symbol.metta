;Number, String, Bool and lists are fixed by their representation: a symbol
;cannot be declared to be a Number.
(: pretend Number)
(: number-id (-> Number Number))
(= (number-id $x) $x)
!(number-id pretend)
