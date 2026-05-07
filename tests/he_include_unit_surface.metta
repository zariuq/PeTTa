!(include support/include_simple)
!(assertEqualToResult (match &self (inc-simple $x) $x) (ok))
