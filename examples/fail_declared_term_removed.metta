;Once the declaration of (dog rex) is removed, (dog rex) is no Animal.
(: Animal Type)
(: name-of (-> Animal Symbol))
(= (name-of $a) named)
(= (pet) (dog rex))
!(add-atom &self (: (dog rex) Animal))
!(test (name-of (pet)) named)
!(remove-atom &self (: (dog rex) Animal))
!(name-of (pet))
