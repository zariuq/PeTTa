;; Attempt to port the propositional calculus of
;;
;; https://us.metamath.org/mpeuni/mmtheorems1.html
;;
;; alongside a few theorems for the backward chainer

;;;;;;;;;
;; Nat ;;
;;;;;;;;;

;; Define Nat
(: Nat Type)
(: Z Nat)
(: S (-> Nat Nat))

;; Define cast functions between Nat and Number
(: fromNumber (-> Number Nat))
(= (fromNumber $n) (if (<= $n 0) Z (S (fromNumber (- $n 1)))))
(: fromNat (-> Nat Number))
(= (fromNat Z) 0)
(= (fromNat (S $k)) (+ 1 (fromNat $k)))

;;;;;;;;;;
;; List ;;
;;;;;;;;;;

;; Commented out because I have them in my other file --sigh--
;; Declaration of List data type and constructors
; (: List (-> $a Type))
; (: Nil (List $a))
; (: Cons (-> $a (List $a) (List $a)))

;;;;;;;;;;;;;;;;;;;;;
;; Match over list ;;
;;;;;;;;;;;;;;;;;;;;;

;; Similar to match but takes a list of terms instead of a space.
(: match' (-> (List Atom) $a $a $a))
(= (match' Nil $pattern $rewrite) (empty))
(= (match' (Cons $head $tail) $pattern $rewrite) (let $pattern $head $rewrite))
(= (match' (Cons $head $tail) $pattern $rewrite) (match' $tail $pattern $rewrite))

;; Test match' on empty list
!(assertEqualToResult
  (match' Nil ($x $y) ($y $x))
  ())

;; Test match' on singleton
!(assertEqual
  (match' (Cons (A B) Nil) ($x $y) ($y $x))
  (B A))

;; Test match' on pair
!(assertEqualToResult
  (match' (Cons (A B) (Cons (C D) Nil)) ($x $y) ($y $x))
  ((B A)
   (D C)))

;; Convert an expression into a list.
; (: to-list (-> Expression (List Atom)))
(= (to-list $expr)
   (if (== $expr ()) Nil
     (Cons (car-atom $expr)
         (to-list (cdr-atom $expr)))))

; (: to-list' (-> Expression (List Atom) (List Atom)))
(= (to-list' $expr $tail)
   (if (== $expr ()) $tail
     (Cons (car-atom $expr)
         (to-list' (cdr-atom $expr) $tail))))

;; Take a list of lists and flatten it.
; (: flatten-list (-> (List Atom) (List Atom)))
(= (flatten-list Nil) Nil)
(= (flatten-list (Cons $head $tail))
  (case (get-metatype $head)
    ((Expression (to-list' $head (flatten-list $tail)))
     ($_ (Cons $head (flatten-list $tail))))))

;; Convert a list into an expression
; (: from-list (-> (List Atom) Expression))
; (: from-list (-> (List $a) Expression))
(= (from-list Nil) ())
(= (from-list (Cons $head $tail))
   (let $tail-list (from-list $tail)
    (cons-atom $head $tail-list)))

;; Flatten an expression
; (: flatten-expr (-> Expression Expression))
(= (flatten-expr $expr) (from-list (flatten-list (to-list $expr))))

(= (filter' Nil $predicate) Nil)
(= (filter' (Cons $head $tail) $predicate)
   (let $tail-result (filter' $tail $predicate)
     (if ($predicate $head)
       (Cons $head $tail-result)
       $tail-result)))

;;;;;;;;;;;;;;;;;;;;;;
;; Backward chainer ;;
;;;;;;;;;;;;;;;;;;;;;;

;; Backward Chainer with environment.  There is no explicit support
;; for lambda abstraction due to the combinatorial explosion resulting
;; from combining lambda abstractions and applications.  Instead,
;; variables are added to the environment manually.  So for instance,
;; if the program to synthesize has the following type signature
;;
;; 𝐁𝐨𝐨𝐥 -> 𝐁𝐨𝐨𝐥 -> 𝐁𝐨𝐨𝐥
;;
;; meaning it is a binary boolean function, thus has 2 arguments, we
;; add the following two declarations in the environment
;;
;; (: z 𝐁𝐨𝐨𝐥)
;; (: (s z) 𝐁𝐨𝐨𝐥)
;;
;; where z and (s z) represents the variables associated with the two
;; arguments.
;;
;; The arguments of the backward chainer are:
;;
;; * Knowledge base: reference to a space containing axioms and rules
;;   in the format (: <NAME> <RULE>).  Rules may or may not be curried
;;   depending on the convenience of the situation.
;;
;; * Environment: a list of typing relationships such as
;;
;;   (Cons (: z 𝐁𝐨𝐨𝐥) (Cons (: (s z) 𝐁𝐨𝐨𝐥) Nil))
;;
;; * Maximum depth: maximum depth of the generated proof tree.
;;
;; * Query: a metta term of the form (: <PROOF> <THEOREM>) where
;;   <PROOF> and <THEOREM> may contain free variables that may be
;;   filled by the backward chainer.
;;
;; A result is the query with its variables grounded, fully or
;; partially.  If multiple results are possible, they are returned as
;; a superposition.
(: bc (-> $a                            ; Knowledge base space
          (List $b)                     ; Environment
          Nat                           ; Maximum depth
          $c                            ; Query
          $c))                          ; Result

;; Compatibility wrapper: 3-arg BC without env
(: bc (-> $kb Nat $q $q))
(= (bc $kb $depth $q) (bc $kb Nil $depth $q))

;; Base cases
;; Match the knowledge base
(= (bc $kb $env $_ (: $proof $theorem))
   (match $kb (: $proof $theorem) (: $proof $theorem)))
;; Match the environment
(= (bc $kb $env $_ (: $proof $theorem))
   (match' $env (: $proof $theorem) (: $proof $theorem)))

;; Recursive step
;; Unary proof application
(= (bc $kb $env (S $k) (: ($rule $arg) $theorem))
   (let* (;; Recurse on unary rule
          ((: $rule (-> $premises $theorem))
           (bc $kb $env $k (: $rule (-> $premises $theorem))))
          ;; Recurse on premise
          ((: $arg $premises)
           (bc $kb $env $k (: $arg $premises))))
     (: ($rule $arg) $theorem)))
;; Binary proof application
(= (bc $kb $env (S $k) (: ($rule $arg1 $arg2) $theorem))
   (let* (;; Recurse on binary rule
          ((: $rule (-> $premises1 $premises2 $theorem))
           (bc $kb $env $k (: $rule (-> $premises1 $premises2 $theorem))))
          ;; Recurse on premise 1
          ((: $arg1 $premises1) (bc $kb $env $k (: $arg1 $premises1)))
          ;; Recurse on premise 2
          ((: $arg2 $premises2) (bc $kb $env $k (: $arg2 $premises2))))
     (: ($rule $arg1 $arg2) $theorem)))

;; Adding env to fc just cuz
(: fc (-> $kb         ; Knowledge base space
          (List $b)   ; Environment
          Nat         ; Maximum depth
          $goal       ; Source expression
          $goal))     ; Resulting conclusions

;; 
;; Just add $env parameter and thread it through
(: fc (-> $kb (List $b) Nat $goal $goal))

;; Base case - no change
(= (fc $kb $env $_ (: $proof $premises))
   (: $proof $premises))

;; Recursive step #1 - just pass $env to bc and fc
(= (fc $kb $env (S $k) (: $arg $premises))
   (let (: $rule (-> $premises $conclusion))
        (bc $kb $env $k (: $rule (-> $premises $conclusion)))
     (fc $kb $env $k (: ($rule $arg) $conclusion))))

;; Recursive step #2 - just pass $env to bc and fc  
(= (fc $kb $env (S $k) (: $rule (-> $premises $conclusion)))
   (let (: $arg $premises)
        (bc $kb $env $k (: $arg $premises))
     (fc $kb $env $k (: ($rule $arg) $conclusion))))

;;;;;;;;;;;;;;;;;;;;
;; Knowledge base ;;
;;;;;;;;;;;;;;;;;;;;

;; Based on https://us.metamath.org/mpeuni/mmtheorems1.html
;;
;; References:
;;
;; [Margaris] Margaris, Angelo, First Order Mathematical Logic,
;; Blaisdell Publishing Company, Waltham, Massachusetts (1967)
;; [QA9.M327].

!(bind! &kb' (new-space))

;; Rule 1 of [Hamilton] p. 73.
;; https://us.metamath.org/mpeuni/ax-mp.html
;  ${
;     $( Minor premise for modus ponens. $)
;     min $e |- ph $.
;     $( Major premise for modus ponens. $)
;     maj $e |- ( ph -> ps ) $.
;     $( Rule of Modus Ponens.  The postulated inference rule of propositional
;        calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  The rule says, "if
;        ` ph ` is true, and ` ph ` implies ` ps ` , then ` ps ` must also be
;        true."  This rule is sometimes called "detachment," since it detaches
;        the minor premise from the major premise.  "Modus ponens" is short for
;        "modus ponendo ponens," a Latin phrase that means "the mood that by
;        affirming affirms" [Sanford] p. 39.  This rule is similar to the rule of
;        modus tollens ~ mto .

;        Note:  In some web page displays such as the Statement List, the symbols
;        "&" and "=>" informally indicate the relationship between the hypotheses
;        and the assertion (conclusion), abbreviating the English words "and" and
;        "implies."  They are not part of the formal language.  (Contributed by
;        NM, 5-Aug-1993.) $)
;     ax-mp $a |- ps $.
;   $}
!(add-atom &kb' (: ax-mp (-> $𝜑 (→ $𝜑 $𝜓) $𝜓)))

;; Axiom Simp. Axiom A1 of [Margaris] p. 49.
;; https://us.metamath.org/mpeuni/ax-1.html
; $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  One of the 3 axioms of
;      propositional calculus.  The 3 axioms are also given as Definition 2.1 of
;      [Hamilton] p. 28.  This axiom is called _Simp_ or "the principle of
;      simplification" in _Principia Mathematica_ (Theorem *2.02 of
;      [WhiteheadRussell] p. 100) because "it enables us to pass from the joint
;      assertion of ` ph ` and ` ps ` to the assertion of ` ph ` simply."
;      (Contributed by NM, 5-Aug-1993.) $)
;   ax-1 $a |- ( ph -> ( ps -> ph ) ) $.
!(add-atom &kb' (: ax-1 (→ $𝜑 (→ $𝜓 $𝜑))))

;; Axiom Frege. Axiom A2 of [Margaris] p. 49.
;; https://us.metamath.org/mpeuni/ax-2.html
; $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  One of the 3 axioms of
;      propositional calculus.  It "distributes" an antecedent over two
;      consequents.  This axiom was part of Frege's original system and is known
;      as _Frege_ in the literature.  It is also proved as Theorem *2.77 of
;      [WhiteheadRussell] p. 108.  The other direction of this axiom also turns
;      out to be true, as demonstrated by ~ pm5.41 .  (Contributed by NM,
;      5-Aug-1993.) $)
;   ax-2 $a |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $.
!(add-atom &kb' (: ax-2 (→ (→ $𝜑 (→ $𝜓 $𝜒)) (→ (→ $𝜑 $𝜓) (→ $𝜑 $𝜒)))))

;; Axiom Transp. Axiom A3 of [Margaris] p. 49.
;; https://us.metamath.org/mpeuni/ax-3.html
;   $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  One of the 3 axioms of
;      propositional calculus.  It swaps or "transposes" the order of the
;      consequents when negation is removed.  An informal example is that the
;      statement "if there are no clouds in the sky, it is not raining" implies
;      the statement "if it is raining, there are clouds in the sky."  This axiom
;      is called _Transp_ or "the principle of transposition" in _Principia
;      Mathematica_ (Theorem *2.17 of [WhiteheadRussell] p. 103).  We will also
;      use the term "contraposition" for this principle, although the reader is
;      advised that in the field of philosophical logic, "contraposition" has a
;      different technical meaning.  (Contributed by NM, 5-Aug-1993.) $)
;   ax-3 $a |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $.
!(add-atom &kb' (: ax-3 (→ (→ (¬ $𝜑) (¬ $𝜓)) (→ $𝜓 $𝜑))))

;;;;;;;;;;
;; Test ;;
;;;;;;;;;;

;; Test subgoal of https://us.metamath.org/mpeuni/mp2.html
;;
;; Note that variables have been replaced by symbols to force them to
;; be different which considerably prunes the search space.
!(bc &kb'
     (Cons (: mp2.1 𝜑)
           (Cons (: mp2.2 𝜓)
                 (Cons (: mp2.3 (→ 𝜑 (→ 𝜓 𝜒)))
                       Nil)))
     (fromNumber 1)
     (: (ax-mp mp2.1 mp2.3) (→ 𝜓 𝜒)))
     ;; (: $proof (→ 𝜓 𝜒)))

;; Test https://us.metamath.org/mpeuni/mp2.html
;;
;; Note that variables have been replaced by symbols to force them to
;; be different which considerably prunes the search space.
!(bc &kb'
     (Cons (: mp2.1 𝜑)
           (Cons (: mp2.2 𝜓)
                 (Cons (: mp2.3 (→ 𝜑 (→ 𝜓 𝜒)))
                       Nil)))
     (fromNumber 2)
     (: (ax-mp mp2.2 (ax-mp mp2.1 mp2.3)) 𝜒))
     ;; (: $proof 𝜒))

;; Test https://us.metamath.org/mpeuni/mp2b.html
;;
;; Note that variables have been replaced by symbols to force them to
;; be different which considerably prunes the search space.
!(bc &kb'
     (Cons (: mp2b.1 𝜑)
           (Cons (: mp2b.2 (→ 𝜑 𝜓))
                 (Cons (: mp2b.3 (→ 𝜓 𝜒))
                       Nil)))
     (fromNumber 2)
     (: (ax-mp (ax-mp mp2b.1 mp2b.2) mp2b.3) 𝜒))
     ;; (: $proof 𝜒))

;; Test https://us.metamath.org/mpeuni/a1i.html
;;
;; Note that variables have been replaced by symbols to force them to
;; be different which considerably prunes the search space.
!(bc &kb'
     (Cons (: a1i.1 𝜑) Nil)
     (fromNumber 1)
     (: (ax-mp a1i.1 ax-1) (→ 𝜓 𝜑)))
     ;; (: $proof (→ 𝜓 𝜑)))
