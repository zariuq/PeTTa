!(println! "Simple test of user space add")
!(bind! &kb (new-space))

!(println! "Direct add-atom to &kb:")
!(add-atom &kb (Test item))

!(println! "")
!(println! "What's in &self:")
!(match &self (subspace kb $x) $x)

!(println! "")
!(println! "Direct match from &kb:")
!(match &kb (Test item) found)