(= (length $x) user-length)
(= (mu:length $x) user-mu-length)

!(assertEqual (length abc) user-length)
!(assertEqual (mu:length abc) user-mu-length)
!(assertEqual (repr (collapse (match &self (= (length $x) $body) $body))) "(user-length)")
!(assertEqual (repr (collapse (match &self (= (mu:length $x) $body) $body))) "(user-mu-length)")
