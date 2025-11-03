!(println! "Testing match with Empty result")
!(bind! &kb (new-space))

!(println! "")
!(println! "Match non-existent pattern:")
!(match &kb (NoSuchThing) found)

!(println! "")
!(println! "Add something and match it:")
!(add-atom &kb (Thing exists))
!(match &kb (Thing exists) found)

!(println! "")
!(println! "Direct test on &self with subspace:")
!(match &self (subspace kb (NoSuchThing)) found)
!(match &self (subspace kb (Thing exists)) found)