;A type can be declared for a compound term. get-type and the checks see such a
;declaration, also when it is added or removed while the program runs.
(: Animal Type)
(: name-of (-> Animal Symbol))
(= (name-of $a) named)
(= (pet) (dog rex))
!(test (collapse (get-type (dog rex))) ((%Undefined% %Undefined%)))
!(add-atom &self (: (dog rex) Animal))
!(test (collapse (get-type (dog rex))) ((%Undefined% %Undefined%) Animal))
!(test (name-of (pet)) named)
!(remove-atom &self (: (dog rex) Animal))
!(test (collapse (get-type (dog rex))) ((%Undefined% %Undefined%)))
