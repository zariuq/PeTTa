!(println! "Testing add_c with debug")
!(bind! &kb (new-space))

(= (has-constant $space $tok)
   (case (match $space (Constant $tok (Type "$c")) found)
     ((Empty False)
      ($_ True))))

(= (add_c $kb $tok)
   (case (has-constant $kb $tok)
     ((True (Error already-exists))
      (False (add-atom $kb (Constant $tok (Type "$c")))))))

!(println! "")
!(println! "Add foo to &kb:")
!(add_c &kb foo)

!(println! "")
!(println! "What's in &self:")
!(match &self $x $x)

!(println! "")
!(println! "Check if foo exists:")
!(has-constant &kb foo)