!(println! "Testing user spaces with subspace fix")
!(println! "")

!(bind! &kb (new-space))
!(bind! &other (new-space))

!(println! "Adding to &kb:")
!(add-atom &kb (Color red))
!(add-atom &kb (Color blue))

!(println! "")
!(println! "Adding to &other:")
!(add-atom &other (Color green))

!(println! "")
!(println! "Match from &kb:")
!(match &kb (Color $x) $x)

!(println! "")
!(println! "Match from &other:")
!(match &other (Color $x) $x)

!(println! "")
!(println! "Verify separation - &kb has red/blue, &other has green")

!(println! "")
!(println! "What's actually in &self:")
!(match &self $x $x)