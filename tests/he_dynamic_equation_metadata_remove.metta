!(add-atom &self (= (tmp-eq-index 1) 2))
!(assertPeTTaTest (tmp-eq-index 1) 2)
!(remove-atom &self (= (tmp-eq-index 1) 2))
!(assertPeTTaTest (tmp-eq-index 1) (tmp-eq-index 1))
