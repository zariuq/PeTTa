!(println! "Testing &self space")
!(println! "")

!(println! "Adding to &self:")
!(add-atom &self (Color red))
!(add-atom &self (Color blue))

!(println! "")
!(println! "Matching from &self:")
!(match &self (Color $x) $x)

!(println! "")
!(println! "Testing tagged subspaces in &self:")
!(add-atom &self (subspace kb (Item A)))
!(add-atom &self (subspace kb (Item B)))
!(add-atom &self (subspace other (Item C)))

!(println! "")
!(println! "Match all kb items:")
!(match &self (subspace kb (Item $x)) $x)

!(println! "")
!(println! "Match all other items:")
!(match &self (subspace other (Item $x)) $x)