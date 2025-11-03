!(println! "Final test of working user spaces")
!(println! "")

;; Don't use bind! - just use the spaces directly
!(println! "Add items to different spaces:")
!(add-atom &kb (Color red))
!(add-atom &kb (Color blue))
!(add-atom &other (Color green))

!(println! "")
!(println! "Match from &kb (should get red and blue):")
!(match &kb (Color $x) $x)

!(println! "")
!(println! "Match from &other (should get green):")
!(match &other (Color $x) $x)

!(println! "")
!(println! "Verify they're stored separately in &self:")
!(match &self (subspace kb $x) $x)
!(println! "")
!(match &self (subspace other $x) $x)