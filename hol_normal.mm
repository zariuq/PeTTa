$( This is the Metamath database hol.mm. $)

$( Metamath is a formal language and associated computer program for
   archiving, verifying, and studying mathematical proofs, created by Norman
   Dwight Megill (1950--2021).  For more information, visit
   https://us.metamath.org and
   https://github.com/metamath/set.mm, and feel free to ask questions at
   https://groups.google.com/g/metamath. $)

$( The database hol.mm was created by Mario Carneiro on 7-Oct-2014. $)


$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file for higher-order logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  https://creativecommons.org/publicdomain/zero/1.0/

Mario Carneiro - email: di.gama at gmail.com

$)


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c var $.   $( Typecode for variables (syntax) $)
  $c type $.  $( Typecode for types (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c . $.     $( Separator $)
  $c |= $.    $( Context separator $)
  $c bool $.  $( Boolean type $)
  $c ind $.   $( 'Individual' type $)
  $c -> $.    $( Function type $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c , $.     $( Context comma $)
  $c \ $.     $( Lambda expression $)
  $c = $.     $( Equality term $)
  $c T. $.    $( Truth term $)
  $c [ $.     $( Infix operator $)
  $c ] $.     $( Infix operator $)

  $v al $.  $( Greek alpha $)
  $v be $.  $( Greek beta $)
  $v ga $.  $( Greek gamma $)
  $v de $.  $( Greek delta $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C F R S T $.  $( Term variables $)

  $( $j syntax 'var' 'type' 'term'; bound 'var'; $)

  $( Let variable ` al ` be a type. $)
  hal $f type al $.
  $( Let variable ` be ` be a type. $)
  hbe $f type be $.
  $( Let variable ` ga ` be a type. $)
  hga $f type ga $.
  $( Let variable ` de ` be a type. $)
  hde $f type de $.

  $( Let variable ` x ` be a var. $)
  vx $f var x $.
  $( Let variable ` y ` be a var. $)
  vy $f var y $.
  $( Let variable ` z ` be a var. $)
  vz $f var z $.
  $( Let variable ` f ` be a var. $)
  vf $f var f $.
  $( Let variable ` g ` be a var. $)
  vg $f var g $.
  $( Let variable ` p ` be a var. $)
  vp $f var p $.
  $( Let variable ` q ` be a var. $)
  vq $f var q $.

  $( Let variable ` A ` be a term. $)
  ta $f term A $.
  $( Let variable ` B ` be a term. $)
  tb $f term B $.
  $( Let variable ` C ` be a term. $)
  tc $f term C $.
  $( Let variable ` F ` be a term. $)
  tf $f term F $.
  $( Let variable ` R ` be a term. $)
  tr $f term R $.
  $( Let variable ` S ` be a term. $)
  ts $f term S $.
  $( Let variable ` T ` be a term. $)
  tt $f term T $.

  $( A var is a term. $)
  tv $a term x : al $.

  $( The type of all functions from type ` al ` to type ` be ` . $)
  ht $a type ( al -> be ) $.
  $( The type of booleans (true and false). $)
  hb $a type bool $.
  $( The type of individuals. $)
  hi $a type ind $.

  $( A combination (function application). $)
  kc $a term ( F T ) $.
  $( A lambda abstraction. $)
  kl $a term \ x : al . T $.
  $( The equality term. $)
  ke $a term = $.
  $( Truth term. $)
  kt $a term T. $.
  $( Infix operator. $)
  kbr $a term [ A F B ] $.
  $( Context operator. $)
  kct $a term ( A , B ) $.

  $c wff $.  $( Not used; for mmj2 compatibility $)

  $( $j syntax 'wff'; syntax '|-' as 'wff'; $)

  $( Internal axiom for mmj2 use. $)
  wffMMJ2 $a wff A |= B $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2t $a wff A : al $.

  ${
    idi.1 $e |- R |= A $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idi $p |- R |= A $=
      idi.1 $.
  $}

  ${
    idt.1 $e |- A : al $.
    $( The identity inference.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    idt $p |- A : al $=
      idt.1 $.
  $}

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-syl $a |- R |= T $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    syl $p |- R |= T $=
      tr ts tt ax-syl.1 ax-syl.2 ax-syl $.
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.
    $( Join common antecedents.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-jca $a |- R |= ( S , T ) $.

    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    jca $p |- R |= ( S , T ) $=
      tr ts tt ax-jca.1 ax-jca.2 ax-jca $.
  $}

  ${
    syl2anc.1 $e |- R |= S $.
    syl2anc.2 $e |- R |= T $.
    syl2anc.3 $e |- ( S , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    syl2anc $p |- R |= A $=
      tr ts tt kct ta tr ts tt syl2anc.1 syl2anc.2 jca syl2anc.3 syl $.
  $}

  ${
    ax-simpl.1 $e |- R : bool $.
    ax-simpl.2 $e |- S : bool $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpl $a |- ( R , S ) |= R $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpr $a |- ( R , S ) |= S $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpl $p |- ( R , S ) |= R $=
      tr ts ax-simpl.1 ax-simpl.2 ax-simpl $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpr $p |- ( R , S ) |= S $=
      tr ts ax-simpl.1 ax-simpl.2 ax-simpr $.
  $}

  ${
    ax-id.1 $e |- R : bool $.
    $( The identity inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-id $a |- R |= R $.

    $( The identity inference.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    id $p |- R |= R $=
      tr ax-id.1 ax-id $.
  $}

  ${
    ax-trud.1 $e |- R : bool $.
    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-trud $a |- R |= T. $.

    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    trud $p |- R |= T. $=
      tr ax-trud.1 ax-trud $.

    ax-a1i.2 $e |- T. |= A $.
    $( Change an empty context into any context.  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    a1i $p |- R |= A $=
      tr kt ta tr ax-trud.1 ax-trud ax-a1i.2 syl $.
  $}

  ${
    ax-cb.1 $e |- R |= A $.
    $( A context has type boolean.

       This and the next few axioms are not strictly necessary, and are
       conservative on any theorem for which every variable has a specified
       type, but by adding this axiom we can save some typehood hypotheses in
       many theorems.  The easy way to see that this axiom is conservative is
       to note that every axiom and inference rule that constructs a theorem of
       the form ` R |= A ` where ` R ` and ` A ` are type variables, also
       ensures that ` R : bool ` and ` A : bool ` .  Thus it is impossible to
       prove any theorem ` |- R |= A ` unless both ` |- R : bool ` and
       ` |- A : bool ` had been previously derived, so it is conservative to
       deduce ` |- R : bool ` from ` |- R |= A ` .  The same remark applies to
       the construction of the theorem ` ( A , B ) : bool ` - there is only one
       rule that creates a formula of this type, namely ~ wct , and it requires
       that ` A : bool ` and ` B : bool ` be previously established, so it is
       safe to reverse the process in ~ wctl and ~ wctr .  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-cb1 $a |- R : bool $.

    $( A theorem has type boolean.  (This axiom is unnecessary; see ~ ax-cb1 .)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-cb2 $a |- A : bool $.
  $}

  ${
    wctl.1 $e |- ( S , T ) : bool $.
    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctl .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctl $a |- S : bool $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctr .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctr $a |- T : bool $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wctl $p |- S : bool $=
      ts tt wctl.1 ax-wctl $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wctr $p |- T : bool $=
      ts tt wctl.1 ax-wctr $.
  $}

  ${
    mpdan.1 $e |- R |= S $.
    mpdan.2 $e |- ( R , S ) |= T $.
    $( Modus ponens deduction.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    mpdan $p |- R |= T $=
      tt tr tr ts tr ts tr mpdan.1 ax-cb1 id mpdan.1 mpdan.2 syl2anc $.
  $}

  ${
    syldan.1 $e |- ( R , S ) |= T $.
    syldan.2 $e |- ( R , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    syldan $p |- ( R , S ) |= A $=
      ta tr ts kct tr tt tr ts tr ts tt tr ts kct syldan.1 ax-cb1 wctl tr ts tt
      tr ts kct syldan.1 ax-cb1 wctr simpl syldan.1 syldan.2 syl2anc $.
  $}

  ${
    simpld.1 $e |- R |= ( S , T ) $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simpld $p |- R |= S $=
      tr ts tt kct ts simpld.1 ts tt ts tt ts tt kct tr simpld.1 ax-cb2 wctl ts
      tt ts tt kct tr simpld.1 ax-cb2 wctr simpl syl $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    simprd $p |- R |= T $=
      tr ts tt kct tt simpld.1 ts tt ts tt ts tt kct tr simpld.1 ax-cb2 wctl ts
      tt ts tt kct tr simpld.1 ax-cb2 wctr simpr syl $.
  $}

  ${
    trul.1 $e |- ( T. , R ) |= S $.
    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    trul $p |- R |= S $=
      ts tr kt tr tr kt tr ts kt tr kct trul.1 ax-cb1 wctr trud tr kt tr ts kt
      tr kct trul.1 ax-cb1 wctr id trul.1 syl2anc $.
  $}

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree.
     (New usage is discouraged.)  (Contributed by Mario Carneiro,
     7-Oct-2014.) $)
  ax-weq $a |- = : ( al -> ( al -> bool ) ) $.

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree.
     (Contributed by Mario Carneiro, 7-Oct-2014.) $)
  weq $p |- = : ( al -> ( al -> bool ) ) $=
    hal ax-weq $.

  ${
    ax-refl.1 $e |- A : al $.
    $( Reflexivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-refl $a |- T. |= ( ( = A ) A ) $.
  $}

  $( Truth type.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
  wtru $p |- T. : bool $=
    ke ke kc ke kc kt hb hb hb ht ht ke hb weq ax-refl ax-cb1 $.

  $( Tautology is provable.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
  tru $p |- T. |= T. $=
    kt wtru id $.

  ${
    ax-eqmp.1 $e |- R |= A $.
    ax-eqmp.2 $e |- R |= ( ( = A ) B ) $.
    $( Modus ponens for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqmp $a |- R |= B $.
  $}

  ${
    ax-ded.1 $e |- ( R , S ) |= T $.
    ax-ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ded $a |- R |= ( ( = S ) T ) $.
  $}

  ${
    wct.1 $e |- S : bool $.
    wct.2 $e |- T : bool $.
    $( The type of a context.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wct $a |- ( S , T ) : bool $.

    $( The type of a context.  (Contributed by Mario Carneiro, 7-Oct-2014.) $)
    wct $p |- ( S , T ) : bool $=
      ts tt wct.1 wct.2 ax-wct $.
  $}

  ${
    wc.1 $e |- F : ( al -> be ) $.
    wc.2 $e |- T : al $.
    $( The type of a combination.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wc $a |- ( F T ) : be $.

    $( The type of a combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    wc $p |- ( F T ) : be $=
      hal hbe tf tt wc.1 wc.2 ax-wc $.
  $}

  ${
    ax-ceq.1 $e |- F : ( al -> be ) $.
    ax-ceq.2 $e |- T : ( al -> be ) $.
    ax-ceq.3 $e |- A : al $.
    ax-ceq.4 $e |- B : al $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ceq $a |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |=
      ( ( = ( F A ) ) ( T B ) ) $.
  $}

  ${
    eqcomx.1 $e |- A : al $.
    eqcomx.2 $e |- B : al $.
    eqcomx.3 $e |- R |= ( ( = A ) B ) $.
    $( Commutativity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqcomx $p |- R |= ( ( = B ) A ) $=
      ke ta kc ta kc ke tb kc ta kc tr ke ta kc ta kc tr ke ta kc tb kc tr
      eqcomx.3 ax-cb1 hal ta eqcomx.1 ax-refl a1i ke ke ta kc ta kc kc ke tb kc
      ta kc kc tr ke ke ta kc kc ke tb kc kc ke ta kc ta kc ke ke ta kc kc ke
      tb kc kc tr ke ke kc ke kc ke ta kc tb kc ke ke kc ke kc tr ke ta kc tb
      kc tr eqcomx.3 ax-cb1 hal hal hb ht ht ke hal weq ax-refl a1i eqcomx.3
      hal hal hb ht ta tb ke ke hal weq hal weq eqcomx.1 eqcomx.2 ax-ceq
      syl2anc ke ta kc ta kc tr ke ta kc tb kc tr eqcomx.3 ax-cb1 hal ta
      eqcomx.1 ax-refl a1i hal hb ta ta ke ta kc ke tb kc hal hal hb ht ke ta
      hal weq eqcomx.1 wc hal hal hb ht ke tb hal weq eqcomx.2 wc eqcomx.1
      eqcomx.1 ax-ceq syl2anc ax-eqmp $.
  $}

  ${
    mpbirx.1 $e |- B : bool $.
    mpbirx.2 $e |- R |= A $.
    mpbirx.3 $e |- R |= ( ( = B ) A ) $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbirx $p |- R |= B $=
      ta tb tr mpbirx.2 hb tb ta tr mpbirx.1 ta tr mpbirx.2 ax-cb2 mpbirx.3
      eqcomx ax-eqmp $.
  $}

  ${
    ancoms.1 $e |- ( R , S ) |= T $.
    $( Swap the two elements of a context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ancoms $p |- ( S , R ) |= T $=
      tt ts tr kct tr ts ts tr tr ts tt tr ts kct ancoms.1 ax-cb1 wctr tr ts tt
      tr ts kct ancoms.1 ax-cb1 wctl simpr ts tr tr ts tt tr ts kct ancoms.1
      ax-cb1 wctr tr ts tt tr ts kct ancoms.1 ax-cb1 wctl simpl ancoms.1
      syl2anc $.
  $}

  ${
    adantr.1 $e |- R |= T $.
    adantr.2 $e |- S : bool $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    adantr $p |- ( R , S ) |= T $=
      tr ts kct tr tt tr ts tt tr adantr.1 ax-cb1 adantr.2 simpl adantr.1 syl
      $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    adantl $p |- ( S , R ) |= T $=
      tr ts tt tr ts tt adantr.1 adantr.2 adantr ancoms $.
  $}

  ${
    ct1.1 $e |- R |= S $.
    ct1.2 $e |- T : bool $.
    $( Introduce a right conjunct.  (Contributed by Mario Carneiro,
       30-Sep-2023.) $)
    ct1 $p |- ( R , T ) |= ( S , T ) $=
      tr tt kct ts tt tr tt ts ct1.1 ct1.2 adantr tr tt ts tr ct1.1 ax-cb1
      ct1.2 simpr jca $.

    $( Introduce a left conjunct.  (Contributed by Mario Carneiro,
       30-Sep-2023.) $)
    ct2 $p |- ( T , R ) |= ( T , S ) $=
      tt tr kct tt ts tt tr ct1.2 ts tr ct1.1 ax-cb1 simpl tr tt ts ct1.1 ct1.2
      adantl jca $.
  $}

  ${
    sylan.1 $e |- R |= S $.
    sylan.2 $e |- ( S , T ) |= A $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    sylan $p |- ( R , T ) |= A $=
      ta tr tt kct ts tt tr tt ts sylan.1 ts tt ta ts tt kct sylan.2 ax-cb1
      wctr adantr tr tt ts tr sylan.1 ax-cb1 ts tt ta ts tt kct sylan.2 ax-cb1
      wctr simpr sylan.2 syl2anc $.
  $}

  ${
    an32s.1 $e |- ( ( R , S ) , T ) |= A $.
    $( Commutation identity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    an32s $p |- ( ( R , T ) , S ) |= A $=
      ta tr tt kct ts kct tr ts kct tt tr tt kct tr ts tr tt tr ts tr ts kct tt
      ta tr ts kct tt kct an32s.1 ax-cb1 wctl wctl tr ts kct tt ta tr ts kct tt
      kct an32s.1 ax-cb1 wctr simpl tr ts tr ts kct tt ta tr ts kct tt kct
      an32s.1 ax-cb1 wctl wctr ct1 tr tt kct ts tt tr tt tr ts tr ts kct tt ta
      tr ts kct tt kct an32s.1 ax-cb1 wctl wctl tr ts kct tt ta tr ts kct tt
      kct an32s.1 ax-cb1 wctr simpr tr ts tr ts kct tt ta tr ts kct tt kct
      an32s.1 ax-cb1 wctl wctr adantr an32s.1 syl2anc $.

    $( Associativity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    anasss $p |- ( R , ( S , T ) ) |= A $=
      ts tt kct tr ta ta ts tr tt ta ts tr kct tr ts kct tt tr ts tr ts kct tr
      ts kct tr ts kct tt ta tr ts kct tt kct an32s.1 ax-cb1 wctl id ancoms
      an32s.1 sylan an32s ancoms $.
  $}

  ${
    anassrs.1 $e |- ( R , ( S , T ) ) |= A $.
    $( Associativity for context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    anassrs $p |- ( ( R , S ) , T ) |= A $=
      ta tr ts kct tt kct tr ts tt kct tr ts kct tt tr tr ts tr ts tt kct ta tr
      ts tt kct kct anassrs.1 ax-cb1 wctl ts tt tr ts tt kct ta tr ts tt kct
      kct anassrs.1 ax-cb1 wctr wctl simpl ts tt tr ts tt kct ta tr ts tt kct
      kct anassrs.1 ax-cb1 wctr wctr adantr tr ts kct ts tt tr ts tr ts tt kct
      ta tr ts tt kct kct anassrs.1 ax-cb1 wctl ts tt tr ts tt kct ta tr ts tt
      kct kct anassrs.1 ax-cb1 wctr wctl simpr ts tt tr ts tt kct ta tr ts tt
      kct kct anassrs.1 ax-cb1 wctr wctr ct1 anassrs.1 syl2anc $.
  $}

  $( The type of a typed variable.  (New usage is discouraged.)  (Contributed
     by Mario Carneiro, 8-Oct-2014.) $)
  ax-wv $a |- x : al : al $.

  $( The type of a typed variable.  (Contributed by Mario Carneiro,
     8-Oct-2014.) $)
  wv $p |- x : al : al $=
    hal vx ax-wv $.

  ${
    wl.1 $e |- T : be $.
    $( The type of a lambda abstraction.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wl $a |- \ x : al . T : ( al -> be ) $.

    $( The type of a lambda abstraction.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wl $p |- \ x : al . T : ( al -> be ) $=
      hal hbe vx tt wl.1 ax-wl $.
  $}

  ${
    ax-beta.1 $e |- A : be $.
    $( Axiom of beta-substitution.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-beta $a |- T. |= ( ( = ( \ x : al . A x : al ) ) A ) $.

    ax-distrc.2 $e |- B : al $.
    ax-distrc.3 $e |- F : ( be -> ga ) $.
    $( Distribution of combination over substitution.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    ax-distrc $a |- T. |= ( ( = ( \ x : al . ( F A ) B ) )
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ) $.
  $}

  ${
    $d x R $.
    ax-leq.1 $e |- A : be $.
    ax-leq.2 $e |- B : be $.
    ax-leq.3 $e |- R |= ( ( = A ) B ) $.
    $( Equality theorem for abstraction.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-leq $a |- R |= ( ( = \ x : al . A ) \ x : al . B ) $.
  $}

  ${
    $d x y $.  $d y B $.
    ax-distrl.1 $e |- A : ga $.
    ax-distrl.2 $e |- B : al $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-distrl $a |- T. |=
      ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) ) $.
  $}

  ${
    wov.1 $e |- F : ( al -> ( be -> ga ) ) $.
    wov.2 $e |- A : al $.
    wov.3 $e |- B : be $.
    $( Type of an infix operator.  (New usage is discouraged.)  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-wov $a |- [ A F B ] : ga $.

    $( Type of an infix operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wov $p |- [ A F B ] : ga $=
      hal hbe hga ta tb tf wov.1 wov.2 wov.3 ax-wov $.

    $( Infix operator.  This is a simple metamath way of cleaning up the syntax
       of all these infix operators to make them a bit more readable than the
       curried representation.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    df-ov $a |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) ) $.
  $}

  ${
    dfov1.1 $e |- F : ( al -> ( be -> bool ) ) $.
    dfov1.2 $e |- A : al $.
    dfov1.3 $e |- B : be $.
    ${
      dfov1.4 $e |- R |= [ A F B ] $.
      $( Forward direction of ~ df-ov .  (Contributed by Mario Carneiro,
         8-Oct-2014.) $)
      dfov1 $p |- R |= ( ( F A ) B ) $=
        ta tb tf kbr tf ta kc tb kc tr dfov1.4 ke ta tb tf kbr kc tf ta kc tb
        kc kc tr ta tb tf kbr tr dfov1.4 ax-cb1 hal hbe hb ta tb tf dfov1.1
        dfov1.2 dfov1.3 df-ov a1i ax-eqmp $.
    $}

    dfov2.4 $e |- R |= ( ( F A ) B ) $.
    $( Reverse direction of ~ df-ov .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    dfov2 $p |- R |= [ A F B ] $=
      tf ta kc tb kc ta tb tf kbr tr hal hbe hb ta tb tf dfov1.1 dfov1.2
      dfov1.3 wov dfov2.4 ke ta tb tf kbr kc tf ta kc tb kc kc tr tf ta kc tb
      kc tr dfov2.4 ax-cb1 hal hbe hb ta tb tf dfov1.1 dfov1.2 dfov1.3 df-ov
      a1i mpbirx $.
  $}

  ${
    weqi.1 $e |- A : al $.
    weqi.2 $e |- B : al $.
    $( Type of an equality.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    weqi $p |- [ A = B ] : bool $=
      hal hal hb ta tb ke hal weq weqi.1 weqi.2 wov $.
  $}

  ${
    eqcomi.1 $e |- A : al $.
    eqcomi.2 $e |- R |= [ A = B ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypi $a |- B : al $.

    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    eqtypi $p |- B : al $=
      hal ta tb tr eqcomi.1 eqcomi.2 ax-eqtypi $.

    $( Commutativity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqcomi $p |- R |= [ B = A ] $=
      hal hal tb ta ke tr hal weq hal ta tb tr eqcomi.1 eqcomi.2 eqtypi
      eqcomi.1 hal ta tb tr eqcomi.1 hal ta tb tr eqcomi.1 eqcomi.2 eqtypi hal
      hal ta tb ke tr hal weq eqcomi.1 hal ta tb tr eqcomi.1 eqcomi.2 eqtypi
      eqcomi.2 dfov1 eqcomx dfov2 $.
  $}

  ${
    eqtypri.1 $e |- A : al $.
    eqtypri.2 $e |- R |= [ B = A ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypri $a |- B : al $.

    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)  (Contributed by Mario
       Carneiro, 7-Oct-2014.) $)
    eqtypri $p |- B : al $=
      hal ta tb tr eqtypri.1 eqtypri.2 ax-eqtypri $.
  $}

  ${
    mpbi.1 $e |- R |= A $.
    mpbi.2 $e |- R |= [ A = B ] $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbi $p |- R |= B $=
      ta tb tr mpbi.1 hb hb ta tb ke tr hb weq ta tr mpbi.1 ax-cb2 hb ta tb tr
      ta tr mpbi.1 ax-cb2 mpbi.2 eqtypi mpbi.2 dfov1 ax-eqmp $.
  $}

  ${
    eqid.1 $e |- R : bool $.
    eqid.2 $e |- A : al $.
    $( Reflexivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqid $p |- R |= [ A = A ] $=
      hal hal ta ta ke tr hal weq eqid.2 eqid.2 ke ta kc ta kc tr eqid.1 hal ta
      eqid.2 ax-refl a1i dfov2 $.
  $}

  ${
    ded.1 $e |- ( R , S ) |= T $.
    ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ded $p |- R |= [ S = T ] $=
      hb hb ts tt ke tr hb weq ts tr tt kct ded.2 ax-cb2 tt tr ts kct ded.1
      ax-cb2 tr ts tt ded.1 ded.2 ax-ded dfov2 $.
  $}

  ${
    dedi.1 $e |- S |= T $.
    dedi.2 $e |- T |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    dedi $p |- T. |= [ S = T ] $=
      kt ts tt ts kt tt dedi.1 wtru adantl tt kt ts dedi.2 wtru adantl ded $.
  $}

  ${
    eqtru.1 $e |- R |= A $.
    $( If a statement is provable, then it is equivalent to truth.
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    eqtru $p |- R |= [ T. = A ] $=
      tr kt ta tr kt ta eqtru.1 wtru adantr kt tr ta kct tr ta ta tr eqtru.1
      ax-cb1 ta tr eqtru.1 ax-cb2 wct tru a1i ded $.
  $}

  ${
    mpbir.1 $e |- R |= A $.
    mpbir.2 $e |- R |= [ B = A ] $.
    $( Deduction from equality inference.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    mpbir $p |- R |= B $=
      ta tb tr mpbir.1 hb tb ta tr hb ta tb tr ta tr mpbir.1 ax-cb2 mpbir.2
      eqtypri mpbir.2 eqcomi mpbi $.
  $}

  ${
    ceq12.1 $e |- F : ( al -> be ) $.
    ceq12.2 $e |- A : al $.
    ${
      ceq12.3 $e |- R |= [ F = T ] $.
      ${
        ceq12.4 $e |- R |= [ A = B ] $.
        $( Equality theorem for combination.  (Contributed by Mario Carneiro,
           7-Oct-2014.) $)
        ceq12 $p |- R |= [ ( F A ) = ( T B ) ] $=
          hbe hbe tf ta kc tt tb kc ke tr hbe weq hal hbe tf ta ceq12.1 ceq12.2
          wc hal hbe tt tb hal hbe ht tf tt tr ceq12.1 ceq12.3 eqtypi hal ta tb
          tr ceq12.2 ceq12.4 eqtypi wc ke tf ta kc kc tt tb kc kc tr ke tf kc
          tt kc ke ta kc tb kc hal hbe ht hal hbe ht tf tt ke tr hal hbe ht weq
          ceq12.1 hal hbe ht tf tt tr ceq12.1 ceq12.3 eqtypi ceq12.3 dfov1 hal
          hal ta tb ke tr hal weq ceq12.2 hal ta tb tr ceq12.2 ceq12.4 eqtypi
          ceq12.4 dfov1 hal hbe ta tb tf tt ceq12.1 hal hbe ht tf tt tr ceq12.1
          ceq12.3 eqtypi ceq12.2 hal ta tb tr ceq12.2 ceq12.4 eqtypi ax-ceq
          syl2anc dfov2 $.
      $}

      $( Equality theorem for combination.  (Contributed by Mario Carneiro,
         7-Oct-2014.) $)
      ceq1 $p |- R |= [ ( F A ) = ( T A ) ] $=
        hal hbe ta ta tf tr tt ceq12.1 ceq12.2 ceq12.3 hal ta tr tf tt ke kbr
        tr ceq12.3 ax-cb1 ceq12.2 eqid ceq12 $.
    $}

    ceq2.3 $e |- R |= [ A = B ] $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ceq2 $p |- R |= [ ( F A ) = ( F B ) ] $=
      hal hbe ta tb tf tr tf ceq12.1 ceq12.2 hal hbe ht tf tr ta tb ke kbr tr
      ceq2.3 ax-cb1 ceq12.1 eqid ceq2.3 ceq12 $.
  $}

  ${
    $d x R $.
    leq.1 $e |- A : be $.
    leq.2 $e |- R |= [ A = B ] $.
    $( Equality theorem for lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    leq $p |- R |= [ \ x : al . A = \ x : al . B ] $=
      hal hbe ht hal hbe ht hal vx ta kl hal vx tb kl ke tr hal hbe ht weq hal
      hbe vx ta leq.1 wl hal hbe vx tb hbe ta tb tr leq.1 leq.2 eqtypi wl hal
      hbe vx ta tb tr leq.1 hbe ta tb tr leq.1 leq.2 eqtypi hbe hbe ta tb ke tr
      hbe weq leq.1 hbe ta tb tr leq.1 leq.2 eqtypi leq.2 dfov1 ax-leq dfov2 $.
  $}

  ${
    beta.1 $e |- A : be $.
    $( Axiom of beta-substitution.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    beta $p |- T. |= [ ( \ x : al . A x : al ) = A ] $=
      hbe hbe hal vx ta kl hal vx tv kc ta ke kt hbe weq hal hbe hal vx ta kl
      hal vx tv hal hbe vx ta beta.1 wl hal vx wv wc beta.1 hal hbe vx ta
      beta.1 ax-beta dfov2 $.
  $}

  ${
    distrc.1 $e |- F : ( be -> ga ) $.
    distrc.2 $e |- A : be $.
    distrc.3 $e |- B : al $.
    $( Distribution of combination over substitution.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    distrc $p |- T. |= [ ( \ x : al . ( F A ) B ) =
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ] $=
      hga hga hal vx tf ta kc kl tb kc hal vx tf kl tb kc hal vx ta kl tb kc kc
      ke kt hga weq hal hga hal vx tf ta kc kl tb hal hga vx tf ta kc hbe hga
      tf ta distrc.1 distrc.2 wc wl distrc.3 wc hbe hga hal vx tf kl tb kc hal
      vx ta kl tb kc hal hbe hga ht hal vx tf kl tb hal hbe hga ht vx tf
      distrc.1 wl distrc.3 wc hal hbe hal vx ta kl tb hal hbe vx ta distrc.2 wl
      distrc.3 wc wc hal hbe hga vx ta tb tf distrc.2 distrc.3 distrc.1
      ax-distrc dfov2 $.
  $}

  ${
    $d x y $.  $d y B $.
    distrl.1 $e |- A : ga $.
    distrl.2 $e |- B : al $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    distrl $p |- T. |=
      [ ( \ x : al . \ y : be . A B ) = \ y : be . ( \ x : al . A B ) ] $=
      hbe hga ht hbe hga ht hal vx hbe vy ta kl kl tb kc hbe vy hal vx ta kl tb
      kc kl ke kt hbe hga ht weq hal hbe hga ht hal vx hbe vy ta kl kl tb hal
      hbe hga ht vx hbe vy ta kl hbe hga vy ta distrl.1 wl wl distrl.2 wc hbe
      hga vy hal vx ta kl tb kc hal hga hal vx ta kl tb hal hga vx ta distrl.1
      wl distrl.2 wc wl hal hbe hga vx vy ta tb distrl.1 distrl.2 ax-distrl
      dfov2 $.
  $}

  ${
    eqtri.1 $e |- A : al $.
    eqtri.2 $e |- R |= [ A = B ] $.
    eqtri.3 $e |- R |= [ B = C ] $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    eqtri $p |- R |= [ A = C ] $=
      hal hal ta tc ke tr hal weq eqtri.1 hal tb tc tr hal ta tb tr eqtri.1
      eqtri.2 eqtypi eqtri.3 eqtypi ke ta kc tb kc ke ta kc tc kc tr hal hal ta
      tb ke tr hal weq eqtri.1 hal ta tb tr eqtri.1 eqtri.2 eqtypi eqtri.2
      dfov1 hal hb tb tc ke ta kc tr hal hal hb ht ke ta hal weq eqtri.1 wc hal
      ta tb tr eqtri.1 eqtri.2 eqtypi eqtri.3 ceq2 mpbi dfov2 $.
  $}

  ${
    3eqtr4i.1 $e |- A : al $.
    3eqtr4i.2 $e |- R |= [ A = B ] $.
    ${
      3eqtr4i.3 $e |- R |= [ S = A ] $.
      3eqtr4i.4 $e |- R |= [ T = B ] $.
      $( Transitivity of equality.  (Contributed by Mario Carneiro,
         7-Oct-2014.) $)
      3eqtr4i $p |- R |= [ S = T ] $=
        hal ts ta tt tr hal ta ts tr 3eqtr4i.1 3eqtr4i.3 eqtypri 3eqtr4i.3 hal
        ta tb tt tr 3eqtr4i.1 3eqtr4i.2 hal tt tb tr hal tb tt tr hal ta tb tr
        3eqtr4i.1 3eqtr4i.2 eqtypi 3eqtr4i.4 eqtypri 3eqtr4i.4 eqcomi eqtri
        eqtri $.
    $}

    3eqtr3i.3 $e |- R |= [ A = S ] $.
    3eqtr3i.4 $e |- R |= [ B = T ] $.
    $( Transitivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    3eqtr3i $p |- R |= [ S = T ] $=
      hal ta tb tr ts tt 3eqtr4i.1 3eqtr4i.2 hal ta ts tr 3eqtr4i.1 3eqtr3i.3
      eqcomi hal tb tt tr hal ta tb tr 3eqtr4i.1 3eqtr4i.2 eqtypi 3eqtr3i.4
      eqcomi 3eqtr4i $.
  $}

  ${
    oveq.1 $e |- F : ( al -> ( be -> ga ) ) $.
    oveq.2 $e |- A : al $.
    oveq.3 $e |- B : be $.
    ${
      oveq123.4 $e |- R |= [ F = S ] $.
      oveq123.5 $e |- R |= [ A = C ] $.
      oveq123.6 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq123 $p |- R |= [ [ A F B ] = [ C S T ] ] $=
        hga tf ta kc tb kc ts tc kc tt kc tr ta tb tf kbr tc tt ts kbr hbe hga
        tf ta kc tb hal hbe hga ht tf ta oveq.1 oveq.2 wc oveq.3 wc hbe hga tb
        tt tf ta kc tr ts tc kc hal hbe hga ht tf ta oveq.1 oveq.2 wc oveq.3
        hal hbe hga ht ta tc tf tr ts oveq.1 oveq.2 oveq123.4 oveq123.5 ceq12
        oveq123.6 ceq12 hga hga ta tb tf kbr tf ta kc tb kc ke tr hga weq hal
        hbe hga ta tb tf oveq.1 oveq.2 oveq.3 wov hbe hga tf ta kc tb hal hbe
        hga ht tf ta oveq.1 oveq.2 wc oveq.3 wc ke ta tb tf kbr kc tf ta kc tb
        kc kc tr tf ts ke kbr tr oveq123.4 ax-cb1 hal hbe hga ta tb tf oveq.1
        oveq.2 oveq.3 df-ov a1i dfov2 hga hga tc tt ts kbr ts tc kc tt kc ke tr
        hga weq hal hbe hga tc tt ts hal hbe hga ht ht tf ts tr oveq.1
        oveq123.4 eqtypi hal ta tc tr oveq.2 oveq123.5 eqtypi hbe tb tt tr
        oveq.3 oveq123.6 eqtypi wov hbe hga ts tc kc tt hal hbe hga ht ts tc
        hal hbe hga ht ht tf ts tr oveq.1 oveq123.4 eqtypi hal ta tc tr oveq.2
        oveq123.5 eqtypi wc hbe tb tt tr oveq.3 oveq123.6 eqtypi wc ke tc tt ts
        kbr kc ts tc kc tt kc kc tr tf ts ke kbr tr oveq123.4 ax-cb1 hal hbe
        hga tc tt ts hal hbe hga ht ht tf ts tr oveq.1 oveq123.4 eqtypi hal ta
        tc tr oveq.2 oveq123.5 eqtypi hbe tb tt tr oveq.3 oveq123.6 eqtypi
        df-ov a1i dfov2 3eqtr4i $.
    $}

    ${
      oveq1.4 $e |- R |= [ A = C ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq1 $p |- R |= [ [ A F B ] = [ C F B ] ] $=
        hal hbe hga ta tb tc tf tr tf tb oveq.1 oveq.2 oveq.3 hal hbe hga ht ht
        tf tr ta tc ke kbr tr oveq1.4 ax-cb1 oveq.1 eqid oveq1.4 hbe tb tr ta
        tc ke kbr tr oveq1.4 ax-cb1 oveq.3 eqid oveq123 $.

      oveq12.5 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq12 $p |- R |= [ [ A F B ] = [ C F T ] ] $=
        hal hbe hga ta tb tc tf tr tf tt oveq.1 oveq.2 oveq.3 hal hbe hga ht ht
        tf tr ta tc ke kbr tr oveq1.4 ax-cb1 oveq.1 eqid oveq1.4 oveq12.5
        oveq123 $.
    $}

    ${
      oveq2.4 $e |- R |= [ B = T ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq2 $p |- R |= [ [ A F B ] = [ A F T ] ] $=
        hal hbe hga ta tb ta tf tr tt oveq.1 oveq.2 oveq.3 hal ta tr tb tt ke
        kbr tr oveq2.4 ax-cb1 oveq.2 eqid oveq2.4 oveq12 $.
    $}

    ${
      oveq.4 $e |- R |= [ F = S ] $.
      $( Equality theorem for binary operation.  (Contributed by Mario
         Carneiro, 7-Oct-2014.) $)
      oveq $p |- R |= [ [ A F B ] = [ A S B ] ] $=
        hal hbe hga ta tb ta tf tr ts tb oveq.1 oveq.2 oveq.3 oveq.4 hal ta tr
        tf ts ke kbr tr oveq.4 ax-cb1 oveq.2 eqid hbe tb tr tf ts ke kbr tr
        oveq.4 ax-cb1 oveq.3 eqid oveq123 $.
    $}
  $}

  ${
    ax-hbl1.1 $e |- A : ga $.
    ax-hbl1.2 $e |- B : al $.
    $( ` x ` is bound in ` \ x A ` .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-hbl1 $a |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $.

    hbl1.3 $e |- R : bool $.
    $( Inference form of ~ ax-hbl1 .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbl1 $p |- R |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $=
      hal vx hbe vx ta kl kl tb kc hbe vx ta kl ke kbr tr hbl1.3 hal hbe hga vx
      ta tb ax-hbl1.1 ax-hbl1.2 ax-hbl1 a1i $.
  $}

  ${
    $d x A $.
    ax-17.1 $e |- A : be $.
    ax-17.2 $e |- B : al $.
    $( If ` x ` does not appear in ` A ` , then any substitution to ` A `
       yields ` A ` again, i.e. ` \ x A ` is a constant function.  (Contributed
       by Mario Carneiro, 8-Oct-2014.) $)
    ax-17 $a |- T. |= [ ( \ x : al . A B ) = A ] $.

    a17i.3 $e |- R : bool $.
    $( Inference form of ~ ax-17 .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    a17i $p |- R |= [ ( \ x : al . A B ) = A ] $=
      hal vx ta kl tb kc ta ke kbr tr a17i.3 hal hbe vx ta tb ax-17.1 ax-17.2
      ax-17 a1i $.
  $}

  ${
    $d x R $.
    hbxfr.1 $e |- T : be $.
    hbxfr.2 $e |- B : al $.
    ${
      hbxfrf.3 $e |- R |= [ T = A ] $.
      hbxfrf.4 $e |- ( S , R ) |= [ ( \ x : al . A B ) = A ] $.
      $( Transfer a hypothesis builder to an equivalent expression.
         (Contributed by Mario Carneiro, 8-Oct-2014.) $)
      hbxfrf $p |- ( S , R ) |= [ ( \ x : al . T B ) = T ] $=
        hbe hal vx ta kl tb kc ta ts tr kct hal vx tt kl tb kc tt hal hbe hal
        vx ta kl tb hal hbe vx ta hbe tt ta tr hbxfr.1 hbxfrf.3 eqtypi wl
        hbxfr.2 wc hbxfrf.4 tr ts hal vx tt kl tb kc hal vx ta kl tb kc ke kbr
        hal hbe tb hal vx tt kl tr hal vx ta kl hal hbe vx tt hbxfr.1 wl
        hbxfr.2 hal hbe vx tt ta tr hbxfr.1 hbxfrf.3 leq ceq1 ts tr hal vx ta
        kl tb kc ta ke kbr ts tr kct hbxfrf.4 ax-cb1 wctl adantl tr ts tt ta ke
        kbr hbxfrf.3 ts tr hal vx ta kl tb kc ta ke kbr ts tr kct hbxfrf.4
        ax-cb1 wctl adantl 3eqtr4i $.
    $}

    hbxfr.3 $e |- R |= [ T = A ] $.
    hbxfr.4 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Transfer a hypothesis builder to an equivalent expression.  (Contributed
       by Mario Carneiro, 8-Oct-2014.) $)
    hbxfr $p |- R |= [ ( \ x : al . T B ) = T ] $=
      hal vx tt kl tb kc tt ke kbr tr tr tr tr tt ta ke kbr tr hbxfr.3 ax-cb1
      id tr tt ta ke kbr tr hbxfr.3 ax-cb1 id hal hbe vx ta tb tr tr tt hbxfr.1
      hbxfr.2 hbxfr.3 tr tr hal vx ta kl tb kc ta ke kbr hbxfr.4 tt ta ke kbr
      tr hbxfr.3 ax-cb1 adantr hbxfrf syl2anc $.
  $}

  ${
    $d x R $.
    hbth.1 $e |- B : al $.
    hbth.2 $e |- R |= A $.
    $( Hypothesis builder for a theorem.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbth $p |- R |= [ ( \ x : al . A B ) = A ] $=
      hal hb vx kt tb tr ta ta tr hbth.2 ax-cb2 hbth.1 hb kt ta tr wtru ta tr
      hbth.2 eqtru eqcomi hal hb vx kt tb tr wtru hbth.1 ta tr hbth.2 ax-cb1
      a17i hbxfr $.
  $}

  ${
    hbc.1 $e |- F : ( be -> ga ) $.
    hbc.2 $e |- A : be $.
    hbc.3 $e |- B : al $.
    hbc.4 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbc.5 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Hypothesis builder for combination.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    hbc $p |- R |= [ ( \ x : al . ( F A ) B ) = ( F A ) ] $=
      hga hal vx tf ta kc kl tb kc hal vx tf kl tb kc hal vx ta kl tb kc kc tf
      ta kc tr hal hga hal vx tf ta kc kl tb hal hga vx tf ta kc hbe hga tf ta
      hbc.1 hbc.2 wc wl hbc.3 wc hal vx tf ta kc kl tb kc hal vx tf kl tb kc
      hal vx ta kl tb kc kc ke kbr tr hal vx tf kl tb kc tf ke kbr tr hbc.4
      ax-cb1 hal hbe hga vx ta tb tf hbc.1 hbc.2 hbc.3 distrc a1i hbe hga hal
      vx ta kl tb kc ta hal vx tf kl tb kc tr tf hal hbe hga ht hal vx tf kl tb
      hal hbe hga ht vx tf hbc.1 wl hbc.3 wc hbe ta hal vx ta kl tb kc tr hbc.2
      hbc.5 eqtypri hbc.4 hbc.5 ceq12 eqtri $.
  $}

  ${
    hbov.1 $e |- F : ( be -> ( ga -> de ) ) $.
    hbov.2 $e |- A : be $.
    hbov.3 $e |- B : al $.
    hbov.4 $e |- C : ga $.
    hbov.5 $e |- R |= [ ( \ x : al . F B ) = F ] $.
    hbov.6 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    hbov.7 $e |- R |= [ ( \ x : al . C B ) = C ] $.
    $( Hypothesis builder for binary operation.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbov $p |- R |= [ ( \ x : al . [ A F C ] B ) = [ A F C ] ] $=
      tr kt hal vx ta tc tf kbr kl tb kc ta tc tf kbr ke kbr tr hal vx tf kl tb
      kc tf ke kbr tr hbov.5 ax-cb1 trud hal hde vx tf ta kc tc kc tb kt tr ta
      tc tf kbr hbe hga hde ta tc tf hbov.1 hbov.2 hbov.4 wov hbov.3 hde hde ta
      tc tf kbr tf ta kc tc kc ke kt hde weq hbe hga hde ta tc tf hbov.1 hbov.2
      hbov.4 wov hga hde tf ta kc tc hbe hga hde ht tf ta hbov.1 hbov.2 wc
      hbov.4 wc hbe hga hde ta tc tf hbov.1 hbov.2 hbov.4 df-ov dfov2 tr kt hal
      vx tf ta kc tc kc kl tb kc tf ta kc tc kc ke kbr hal hga hde vx tc tb tf
      ta kc tr hbe hga hde ht tf ta hbov.1 hbov.2 wc hbov.4 hbov.3 hal hbe hga
      hde ht vx ta tb tf tr hbov.1 hbov.2 hbov.3 hbov.5 hbov.6 hbc hbov.7 hbc
      wtru adantr hbxfrf mpdan $.
  $}

  ${
    $d x y $.  $d y B $.  $d y R $.
    hbl.1 $e |- A : ga $.
    hbl.2 $e |- B : al $.
    hbl.3 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    $( Hypothesis builder for lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbl $p |- R |= [ ( \ x : al . \ y : be . A B ) = \ y : be . A ] $=
      hbe hga ht hal vx hbe vy ta kl kl tb kc hbe vy hal vx ta kl tb kc kl hbe
      vy ta kl tr hal hbe hga ht hal vx hbe vy ta kl kl tb hal hbe hga ht vx
      hbe vy ta kl hbe hga vy ta hbl.1 wl wl hbl.2 wc hal vx hbe vy ta kl kl tb
      kc hbe vy hal vx ta kl tb kc kl ke kbr tr hal vx ta kl tb kc ta ke kbr tr
      hbl.3 ax-cb1 hal hbe hga vx vy ta tb hbl.1 hbl.2 distrl a1i hbe hga vy
      hal vx ta kl tb kc ta tr hal hga hal vx ta kl tb hal hga vx ta hbl.1 wl
      hbl.2 wc hbl.3 leq eqtri $.
  $}

  ${
    $d x y $.  $d y B $.  $d y S $.
    ax-inst.1 $e |- R |= A $.
    ax-inst.2 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    ax-inst.3 $e |- T. |= [ ( \ x : al . S y : al ) = S ] $.
    ax-inst.4 $e |- [ x : al = C ] |= [ A = B ] $.
    ax-inst.5 $e |- [ x : al = C ] |= [ R = S ] $.
    $( Instantiate a theorem with a new term.  The second and third hypotheses
       are the HOL equivalent of set.mm "effectively not free in" predicate
       (see set.mm's ax-17, or ~ ax17m ).  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-inst $a |- S |= B $.
  $}

  ${
    $d x y R $.  $d y B $.
    insti.1 $e |- C : al $.
    insti.2 $e |- B : bool $.
    insti.3 $e |- R |= A $.
    insti.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    insti.5 $e |- [ x : al = C ] |= [ A = B ] $.
    $( Instantiate a theorem with a new term.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    insti $p |- R |= B $=
      hal vx vy ta tb tc tr tr insti.3 insti.4 hal hb vx tr hal vy tv ta tr
      insti.3 ax-cb1 hal vy wv ax-17 insti.5 hb tr hal vx tv tc ke kbr ta tb ke
      kbr hal vx tv tc ke kbr insti.5 ax-cb1 ta tr insti.3 ax-cb1 eqid ax-inst
      $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d x y al $.
    clf.1 $e |- A : be $.
    clf.2 $e |- C : al $.
    clf.3 $e |- [ x : al = C ] |= [ A = B ] $.
    clf.4 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    clf.5 $e |- T. |= [ ( \ x : al . C y : al ) = C ] $.
    $( Evaluate a lambda expression.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    clf $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      hal vx vy hal vx ta kl hal vx tv kc ta ke kbr hal vx ta kl tc kc tb ke
      kbr tc kt clf.2 hbe hal vx ta kl tc kc tb hal hbe hal vx ta kl tc hal hbe
      vx ta clf.1 wl clf.2 wc hbe ta tb hal vx tv tc ke kbr clf.1 clf.3 eqtypi
      weqi hal vx ta kl hal vx tv kc ta ke kbr kt hal vx tb kl hal vy tv kc tb
      ke kbr kt clf.4 ax-cb1 hal hbe vx ta clf.1 beta a1i hal hbe hbe hb vx hal
      vx ta kl tc kc hal vy tv tb ke kt hbe weq hal hbe hal vx ta kl tc hal hbe
      vx ta clf.1 wl clf.2 wc hal vy wv hbe ta tb hal vx tv tc ke kbr clf.1
      clf.3 eqtypi hal hbe hbe hb ht ht vx ke hal vy tv kt hbe weq hal vy wv
      hal vx tb kl hal vy tv kc tb ke kbr kt clf.4 ax-cb1 a17i hal hal hbe vx
      tc hal vy tv hal vx ta kl kt hal hbe vx ta clf.1 wl clf.2 hal vy wv hal
      hal hbe vx ta hal vy tv kt clf.1 hal vy wv hal vx tb kl hal vy tv kc tb
      ke kbr kt clf.4 ax-cb1 hbl1 clf.5 hbc clf.4 hbov hbe hbe hb hal vx ta kl
      hal vx tv kc ta hal vx ta kl tc kc ke hal vx tv tc ke kbr tb hbe weq hal
      hbe hal vx ta kl hal vx tv hal hbe vx ta clf.1 wl hal vx wv wc clf.1 hal
      hbe hal vx tv tc hal vx ta kl hal vx tv tc ke kbr hal hbe vx ta clf.1 wl
      hal vx wv hal vx tv tc ke kbr hal hal vx tv tc hal vx wv clf.2 weqi id
      ceq2 clf.3 oveq12 insti $.
  $}

  ${
    $d y A $.  $d x y B $.  $d x y C $.  $d x y al $.
    cl.1 $e |- A : be $.
    cl.2 $e |- C : al $.
    cl.3 $e |- [ x : al = C ] |= [ A = B ] $.
    $( Evaluate a lambda expression.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    cl $p |- T. |= [ ( \ x : al . A C ) = B ] $=
      hal hbe vx vy ta tb tc cl.1 cl.2 cl.3 hal hbe vx tb hal vy tv hbe ta tb
      hal vx tv tc ke kbr cl.1 cl.3 eqtypi hal vy wv ax-17 hal hal vx tc hal vy
      tv cl.2 hal vy wv ax-17 clf $.
  $}

  ${
    $d x B $.  $d y C $.  $d x y S $.  $d y T $.  $d x al $.  $d y be $.
    ovl.1 $e |- A : ga $.
    ovl.2 $e |- S : al $.
    ovl.3 $e |- T : be $.
    ovl.4 $e |- [ x : al = S ] |= [ A = B ] $.
    ovl.5 $e |- [ y : be = T ] |= [ B = C ] $.
    $( Evaluate a lambda expression in a binary operation.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ovl $p |- T. |= [ [ S \ x : al . \ y : be . A T ] = C ] $=
      hga ts tt hal vx hbe vy ta kl kl kbr hbe vy hal vx ta kl ts kc kl tt kc
      tc kt hal hbe hga ts tt hal vx hbe vy ta kl kl hal hbe hga ht vx hbe vy
      ta kl hbe hga vy ta ovl.1 wl wl ovl.2 ovl.3 wov hga ts tt hal vx hbe vy
      ta kl kl kbr hal vx hbe vy ta kl kl ts kc tt kc hbe vy hal vx ta kl ts kc
      kl tt kc kt hal hbe hga ts tt hal vx hbe vy ta kl kl hal hbe hga ht vx
      hbe vy ta kl hbe hga vy ta ovl.1 wl wl ovl.2 ovl.3 wov hga hga ts tt hal
      vx hbe vy ta kl kl kbr hal vx hbe vy ta kl kl ts kc tt kc ke kt hga weq
      hal hbe hga ts tt hal vx hbe vy ta kl kl hal hbe hga ht vx hbe vy ta kl
      hbe hga vy ta ovl.1 wl wl ovl.2 ovl.3 wov hbe hga hal vx hbe vy ta kl kl
      ts kc tt hal hbe hga ht hal vx hbe vy ta kl kl ts hal hbe hga ht vx hbe
      vy ta kl hbe hga vy ta ovl.1 wl wl ovl.2 wc ovl.3 wc ke ts tt hal vx hbe
      vy ta kl kl kbr kc hal vx hbe vy ta kl kl ts kc tt kc kc kt wtru hal hbe
      hga ts tt hal vx hbe vy ta kl kl hal hbe hga ht vx hbe vy ta kl hbe hga
      vy ta ovl.1 wl wl ovl.2 ovl.3 df-ov a1i dfov2 hbe hga tt hal vx hbe vy ta
      kl kl ts kc kt hbe vy hal vx ta kl ts kc kl hal hbe hga ht hal vx hbe vy
      ta kl kl ts hal hbe hga ht vx hbe vy ta kl hbe hga vy ta ovl.1 wl wl
      ovl.2 wc ovl.3 hal vx hbe vy ta kl kl ts kc hbe vy hal vx ta kl ts kc kl
      ke kbr kt wtru hal hbe hga vx vy ta ts ovl.1 ovl.2 distrl a1i ceq1 eqtri
      hbe hga vy hal vx ta kl ts kc tc tt hal hga hal vx ta kl ts hal hga vx ta
      ovl.1 wl ovl.2 wc ovl.3 hga hal vx ta kl ts kc tb tc hbe vy tv tt ke kbr
      hal hga hal vx ta kl ts hal hga vx ta ovl.1 wl ovl.2 wc hal vx ta kl ts
      kc tb ke kbr hbe vy tv tt ke kbr hbe hbe vy tv tt hbe vy wv ovl.3 weqi
      hal hga vx ta tb ts ovl.1 ovl.2 ovl.4 cl a1i ovl.5 eqtri cl eqtri $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Add propositional calculus definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c F. $.   $( Contradiction term $)
  $c /\ $.   $( Conjunction term $)
  $c ~ $.    $( Negation term $)
  $c ==> $.  $( Implication term $)
  $c ! $.    $( For all term $)
  $c ? $.    $( There exists term $)
  $c \/ $.   $( Disjunction term $)
  $c ?! $.   $( There exists unique term $)

  $( Contradiction term. $)
  tfal $a term F. $.
  $( Conjunction term. $)
  tan $a term /\ $.
  $( Negation term. $)
  tne $a term ~ $.
  $( Implication term. $)
  tim $a term ==> $.
  $( For all term. $)
  tal $a term ! $.
  $( There exists term. $)
  tex $a term ? $.
  $( Disjunction term. $)
  tor $a term \/ $.
  $( There exists unique term. $)
  teu $a term ?! $.

  ${
    $d f p q x y $.
    $( Define the for all operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-al $a |- T. |=
      [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ] $.

    $( Define the constant false.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-fal $a |- T. |= [ F. = ( ! \ p : bool . p : bool ) ] $.

    $( Define the 'and' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-an $a |- T. |=
        [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) .
        [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] =
          \ f : ( bool -> ( bool -> bool ) ) .
            [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $.

    $( Define the implication operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-im $a |- T. |= [ ==> =
      \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ] $.

    $( Define the negation operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-not $a |- T. |= [ ~ = \ p : bool . [ p : bool ==> F. ] ] $.

    $( Define the existence operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-ex $a |- T. |= [ ? = \ p : ( al -> bool ) .
      ( ! \ q : bool . [ ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ] $.

    $( Define the 'or' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-or $a |- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool .
        [ [ p : bool ==> x : bool ] ==>
          [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ] $.

    $( Define the 'exists unique' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-eu $a |- T. |= [ ?! = \ p : ( al -> bool ) .
      ( ? \ y : al . ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ] $.
  $}

  ${
    $d f p q x y $.
    $( For all type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wal $p |- ! : ( ( al -> bool ) -> bool ) $=
      hal hb ht hb ht hal hb ht vp hal hb ht vp tv hal vx kt kl ke kbr kl tal
      kt hal hb ht hb vp hal hb ht vp tv hal vx kt kl ke kbr hal hb ht hal hb
      ht vp tv hal vx kt kl hal hb ht vp wv hal hb vx kt wtru wl weqi wl hal vx
      vp df-al eqtypri $.

    $( Contradiction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wfal $p |- F. : bool $=
      hb tal hb vp hb vp tv kl kc tfal kt hb hb ht hb tal hb vp hb vp tv kl hb
      wal hb hb vp hb vp tv hb vp wv wl wc vp df-fal eqtypri $.

    $( Conjunction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wan $p |- /\ : ( bool -> ( bool -> bool ) ) $=
      hb hb hb ht ht hb vp hb vq hb hb hb ht ht vf hb vp tv hb vq tv hb hb hb
      ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke
      kbr kl kl tan kt hb hb hb ht vp hb vq hb hb hb ht ht vf hb vp tv hb vq tv
      hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv
      kbr kl ke kbr kl hb hb vq hb hb hb ht ht vf hb vp tv hb vq tv hb hb hb ht
      ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke
      kbr hb hb hb ht ht hb ht hb hb hb ht ht vf hb vp tv hb vq tv hb hb hb ht
      ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl hb hb
      hb ht ht hb vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr hb hb hb hb vp
      tv hb vq tv hb hb hb ht ht vf tv hb hb hb ht ht vf wv hb vp wv hb vq wv
      wov wl hb hb hb ht ht hb vf kt kt hb hb hb ht ht vf tv kbr hb hb hb kt kt
      hb hb hb ht ht vf tv hb hb hb ht ht vf wv wtru wtru wov wl weqi wl wl vf
      vp vq df-an eqtypri $.

    $( Implication type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wim $p |- ==> : ( bool -> ( bool -> bool ) ) $=
      hb hb hb ht ht hb vp hb vq hb vp tv hb vq tv tan kbr hb vp tv ke kbr kl
      kl tim kt hb hb hb ht vp hb vq hb vp tv hb vq tv tan kbr hb vp tv ke kbr
      kl hb hb vq hb vp tv hb vq tv tan kbr hb vp tv ke kbr hb hb vp tv hb vq
      tv tan kbr hb vp tv hb hb hb hb vp tv hb vq tv tan wan hb vp wv hb vq wv
      wov hb vp wv weqi wl wl vp vq df-im eqtypri $.

    $( Negation type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wnot $p |- ~ : ( bool -> bool ) $=
      hb hb ht hb vp hb vp tv tfal tim kbr kl tne kt hb hb vp hb vp tv tfal tim
      kbr hb hb hb hb vp tv tfal tim wim hb vp wv wfal wov wl vp df-not eqtypri
      $.

    $( There exists type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wex $p |- ? : ( ( al -> bool ) -> bool ) $=
      hal hb ht hb ht hal hb ht vp tal hb vq tal hal vx hal hb ht vp tv hal vx
      tv kc hb vq tv tim kbr kl kc hb vq tv tim kbr kl kc kl tex kt hal hb ht
      hb vp tal hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr
      kl kc hb vq tv tim kbr kl kc hb hb ht hb tal hb vq tal hal vx hal hb ht
      vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv tim kbr kl hb wal hb
      hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb
      vq tv tim kbr hb hb hb tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv
      tim kbr kl kc hb vq tv tim wim hal hb ht hb tal hal vx hal hb ht vp tv
      hal vx tv kc hb vq tv tim kbr kl hal wal hal hb vx hal hb ht vp tv hal vx
      tv kc hb vq tv tim kbr hb hb hb hal hb ht vp tv hal vx tv kc hb vq tv tim
      wim hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hb vq
      wv wov wl wc hb vq wv wov wl wc wl hal vx vp vq df-ex eqtypri $.

    $( Disjunction type.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    wor $p |- \/ : ( bool -> ( bool -> bool ) ) $=
      hb hb hb ht ht hb vp hb vq tal hb vx hb vp tv hb vx tv tim kbr hb vq tv
      hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc kl kl tor kt hb hb hb ht
      vp hb vq tal hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb
      vx tv tim kbr tim kbr kl kc kl hb hb vq tal hb vx hb vp tv hb vx tv tim
      kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc hb hb ht hb
      tal hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv
      tim kbr tim kbr kl hb wal hb hb vx hb vp tv hb vx tv tim kbr hb vq tv hb
      vx tv tim kbr hb vx tv tim kbr tim kbr hb hb hb hb vp tv hb vx tv tim kbr
      hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb hb vp tv hb
      vx tv tim wim hb vp wv hb vx wv wov hb hb hb hb vq tv hb vx tv tim kbr hb
      vx tv tim wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov hb
      vx wv wov wov wl wc wl wl vx vp vq df-or eqtypri $.

    $( There exists unique type.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    weu $p |- ?! : ( ( al -> bool ) -> bool ) $=
      hal hb ht hb ht hal hb ht vp tex hal vy tal hal vx hal hb ht vp tv hal vx
      tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl kc kl teu kt hal hb ht
      hb vp tex hal vy tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy
      tv ke kbr ke kbr kl kc kl kc hal hb ht hb tex hal vy tal hal vx hal hb ht
      vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl hal wex hal
      hb vy tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr
      ke kbr kl kc hal hb ht hb tal hal vx hal hb ht vp tv hal vx tv kc hal vx
      tv hal vy tv ke kbr ke kbr kl hal wal hal hb vx hal hb ht vp tv hal vx tv
      kc hal vx tv hal vy tv ke kbr ke kbr hb hal hb ht vp tv hal vx tv kc hal
      vx tv hal vy tv ke kbr hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv
      hal vx wv wc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi weqi wl wc
      wl wc wl hal vx vy vp df-eu eqtypri $.
  $}

  ${
    $d p q x y al $.  $d p q y F $.
    alval.1 $e |- F : ( al -> bool ) $.
    $( Value of the for all predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    alval $p |- T. |= [ ( ! F ) = [ F = \ x : al . T. ] ] $=
      hb tal tf kc hal hb ht vp hal hb ht vp tv hal vx kt kl ke kbr kl tf kc tf
      hal vx kt kl ke kbr kt hal hb ht hb tal tf hal wal alval.1 wc hal hb ht
      hb tf tal kt hal hb ht vp hal hb ht vp tv hal vx kt kl ke kbr kl hal wal
      alval.1 hal vx vp df-al ceq1 hal hb ht hb vp hal hb ht vp tv hal vx kt kl
      ke kbr tf hal vx kt kl ke kbr tf hal hb ht hal hb ht vp tv hal vx kt kl
      hal hb ht vp wv hal hb vx kt wtru wl weqi alval.1 hal hb ht hal hb ht hb
      hal hb ht vp tv hal vx kt kl tf ke hal hb ht vp tv tf ke kbr hal hb ht
      weq hal hb ht vp wv hal hb vx kt wtru wl hal hb ht vp tv tf ke kbr hal hb
      ht hal hb ht vp tv tf hal hb ht vp wv alval.1 weqi id oveq1 cl eqtri $.

    $d x F $.
    $( Value of the 'there exists' predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    exval $p |- T. |= [ ( ? F ) = ( ! \ q : bool . [ ( ! \ x : al .
        [ ( F x : al ) ==> q : bool ] ) ==> q : bool ] ) ] $=
      hb tex tf kc hal hb ht vp tal hb vq tal hal vx hal hb ht vp tv hal vx tv
      kc hb vq tv tim kbr kl kc hb vq tv tim kbr kl kc kl tf kc tal hb vq tal
      hal vx tf hal vx tv kc hb vq tv tim kbr kl kc hb vq tv tim kbr kl kc kt
      hal hb ht hb tex tf hal wex alval.1 wc hal hb ht hb tf tex kt hal hb ht
      vp tal hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl
      kc hb vq tv tim kbr kl kc kl hal wex alval.1 hal vx vp vq df-ex ceq1 hal
      hb ht hb vp tal hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv
      tim kbr kl kc hb vq tv tim kbr kl kc tal hb vq tal hal vx tf hal vx tv kc
      hb vq tv tim kbr kl kc hb vq tv tim kbr kl kc tf hb hb ht hb tal hb vq
      tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv
      tim kbr kl hb wal hb hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq
      tv tim kbr kl kc hb vq tv tim kbr hb hb hb tal hal vx hal hb ht vp tv hal
      vx tv kc hb vq tv tim kbr kl kc hb vq tv tim wim hal hb ht hb tal hal vx
      hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl hal wal hal hb vx hal hb
      ht vp tv hal vx tv kc hb vq tv tim kbr hb hb hb hal hb ht vp tv hal vx tv
      kc hb vq tv tim wim hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal
      vx wv wc hb vq wv wov wl wc hb vq wv wov wl wc alval.1 hb hb ht hb hb vq
      tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv
      tim kbr kl hb vq tal hal vx tf hal vx tv kc hb vq tv tim kbr kl kc hb vq
      tv tim kbr kl tal hal hb ht vp tv tf ke kbr hb wal hb hb vq tal hal vx
      hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv tim kbr hb
      hb hb tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb
      vq tv tim wim hal hb ht hb tal hal vx hal hb ht vp tv hal vx tv kc hb vq
      tv tim kbr kl hal wal hal hb vx hal hb ht vp tv hal vx tv kc hb vq tv tim
      kbr hb hb hb hal hb ht vp tv hal vx tv kc hb vq tv tim wim hal hb hal hb
      ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hb vq wv wov wl wc hb vq
      wv wov wl hb hb vq tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim
      kbr kl kc hb vq tv tim kbr tal hal vx tf hal vx tv kc hb vq tv tim kbr kl
      kc hb vq tv tim kbr hal hb ht vp tv tf ke kbr hb hb hb tal hal vx hal hb
      ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv tim wim hal hb ht
      hb tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl hal wal
      hal hb vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr hb hb hb hal hb
      ht vp tv hal vx tv kc hb vq tv tim wim hal hb hal hb ht vp tv hal vx tv
      hal hb ht vp wv hal vx wv wc hb vq wv wov wl wc hb vq wv wov hb hb hb tal
      hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl kc hb vq tv tal
      hal vx tf hal vx tv kc hb vq tv tim kbr kl kc tim hal hb ht vp tv tf ke
      kbr wim hal hb ht hb tal hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim
      kbr kl hal wal hal hb vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr hb
      hb hb hal hb ht vp tv hal vx tv kc hb vq tv tim wim hal hb hal hb ht vp
      tv hal vx tv hal hb ht vp wv hal vx wv wc hb vq wv wov wl wc hb vq wv hal
      hb ht hb hal vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr kl hal vx
      tf hal vx tv kc hb vq tv tim kbr kl tal hal hb ht vp tv tf ke kbr hal wal
      hal hb vx hal hb ht vp tv hal vx tv kc hb vq tv tim kbr hb hb hb hal hb
      ht vp tv hal vx tv kc hb vq tv tim wim hal hb hal hb ht vp tv hal vx tv
      hal hb ht vp wv hal vx wv wc hb vq wv wov wl hal hb vx hal hb ht vp tv
      hal vx tv kc hb vq tv tim kbr tf hal vx tv kc hb vq tv tim kbr hal hb ht
      vp tv tf ke kbr hb hb hb hal hb ht vp tv hal vx tv kc hb vq tv tim wim
      hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hb vq wv
      wov hb hb hb hal hb ht vp tv hal vx tv kc hb vq tv tf hal vx tv kc tim
      hal hb ht vp tv tf ke kbr wim hal hb hal hb ht vp tv hal vx tv hal hb ht
      vp wv hal vx wv wc hb vq wv hal hb hal vx tv hal hb ht vp tv hal hb ht vp
      tv tf ke kbr tf hal hb ht vp wv hal vx wv hal hb ht vp tv tf ke kbr hal
      hb ht hal hb ht vp tv tf hal hb ht vp wv alval.1 weqi id ceq1 oveq1 leq
      ceq2 oveq1 leq ceq2 cl eqtri $.

    $( Value of the 'exists unique' predicate.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    euval $p |- T. |= [ ( ?! F ) = ( ? \ y : al . ( ! \ x : al .
        [ ( F x : al ) = [ x : al = y : al ] ] ) ) ] $=
      hb teu tf kc hal hb ht vp tex hal vy tal hal vx hal hb ht vp tv hal vx tv
      kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl kc kl tf kc tex hal vy tal
      hal vx tf hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl kc kt
      hal hb ht hb teu tf hal weu alval.1 wc hal hb ht hb tf teu kt hal hb ht
      vp tex hal vy tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv
      ke kbr ke kbr kl kc kl kc kl hal weu alval.1 hal vx vy vp df-eu ceq1 hal
      hb ht hb vp tex hal vy tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv
      hal vy tv ke kbr ke kbr kl kc kl kc tex hal vy tal hal vx tf hal vx tv kc
      hal vx tv hal vy tv ke kbr ke kbr kl kc kl kc tf hal hb ht hb tex hal vy
      tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr
      kl kc kl hal wex hal hb vy tal hal vx hal hb ht vp tv hal vx tv kc hal vx
      tv hal vy tv ke kbr ke kbr kl kc hal hb ht hb tal hal vx hal hb ht vp tv
      hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl hal wal hal hb vx hal
      hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr hb hal hb ht
      vp tv hal vx tv kc hal vx tv hal vy tv ke kbr hal hb hal hb ht vp tv hal
      vx tv hal hb ht vp wv hal vx wv wc hal hal vx tv hal vy tv hal vx wv hal
      vy wv weqi weqi wl wc wl wc alval.1 hal hb ht hb hal vy tal hal vx hal hb
      ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl hal vy
      tal hal vx tf hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc kl tex
      hal hb ht vp tv tf ke kbr hal wex hal hb vy tal hal vx hal hb ht vp tv
      hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc hal hb ht hb tal hal
      vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl hal
      wal hal hb vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke
      kbr hb hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr hal hb hal
      hb ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hal hal vx tv hal vy
      tv hal vx wv hal vy wv weqi weqi wl wc wl hal hb vy tal hal vx hal hb ht
      vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc tal hal vx tf
      hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl kc hal hb ht vp tv tf
      ke kbr hal hb ht hb tal hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal
      vy tv ke kbr ke kbr kl hal wal hal hb vx hal hb ht vp tv hal vx tv kc hal
      vx tv hal vy tv ke kbr ke kbr hb hal hb ht vp tv hal vx tv kc hal vx tv
      hal vy tv ke kbr hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal vx
      wv wc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi weqi wl wc hal hb
      ht hb hal vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke
      kbr kl hal vx tf hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr kl tal
      hal hb ht vp tv tf ke kbr hal wal hal hb vx hal hb ht vp tv hal vx tv kc
      hal vx tv hal vy tv ke kbr ke kbr hb hal hb ht vp tv hal vx tv kc hal vx
      tv hal vy tv ke kbr hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal
      vx wv wc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi weqi wl hal hb
      vx hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr ke kbr tf hal
      vx tv kc hal vx tv hal vy tv ke kbr ke kbr hal hb ht vp tv tf ke kbr hb
      hal hb ht vp tv hal vx tv kc hal vx tv hal vy tv ke kbr hal hb hal hb ht
      vp tv hal vx tv hal hb ht vp wv hal vx wv wc hal hal vx tv hal vy tv hal
      vx wv hal vy wv weqi weqi hb hb hb hal hb ht vp tv hal vx tv kc hal vx tv
      hal vy tv ke kbr tf hal vx tv kc ke hal hb ht vp tv tf ke kbr hb weq hal
      hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hal hal vx tv
      hal vy tv hal vx wv hal vy wv weqi hal hb hal vx tv hal hb ht vp tv hal
      hb ht vp tv tf ke kbr tf hal hb ht vp wv hal vx wv hal hb ht vp tv tf ke
      kbr hal hb ht hal hb ht vp tv tf hal hb ht vp wv alval.1 weqi id ceq1
      oveq1 leq ceq2 leq ceq2 cl eqtri $.
  $}

  ${
    $d f p q x A $.  $d f q x B $.
    imval.1 $e |- A : bool $.
    $( Value of negation.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    notval $p |- T. |= [ ( ~ A ) = [ A ==> F. ] ] $=
      hb tne ta kc hb vp hb vp tv tfal tim kbr kl ta kc ta tfal tim kbr kt hb
      hb tne ta wnot imval.1 wc hb hb ta tne kt hb vp hb vp tv tfal tim kbr kl
      wnot imval.1 vp df-not ceq1 hb hb vp hb vp tv tfal tim kbr ta tfal tim
      kbr ta hb hb hb hb vp tv tfal tim wim hb vp wv wfal wov imval.1 hb hb hb
      hb vp tv tfal ta tim hb vp tv ta ke kbr wim hb vp wv wfal hb vp tv ta ke
      kbr hb hb vp tv ta hb vp wv imval.1 weqi id oveq1 cl eqtri $.

    imval.2 $e |- B : bool $.
    $( Value of the implication.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    imval $p |- T. |= [ [ A ==> B ] = [ [ A /\ B ] = A ] ] $=
      hb ta tb tim kbr ta tb hb vp hb vq hb vp tv hb vq tv tan kbr hb vp tv ke
      kbr kl kl kbr ta tb tan kbr ta ke kbr kt hb hb hb ta tb tim wim imval.1
      imval.2 wov hb hb hb ta tb tim kt hb vp hb vq hb vp tv hb vq tv tan kbr
      hb vp tv ke kbr kl kl wim imval.1 imval.2 vp vq df-im oveq hb hb hb vp vq
      hb vp tv hb vq tv tan kbr hb vp tv ke kbr ta hb vq tv tan kbr ta ke kbr
      ta tb tan kbr ta ke kbr ta tb hb hb vp tv hb vq tv tan kbr hb vp tv hb hb
      hb hb vp tv hb vq tv tan wan hb vp wv hb vq wv wov hb vp wv weqi imval.1
      imval.2 hb hb hb hb vp tv hb vq tv tan kbr hb vp tv ta hb vq tv tan kbr
      ke hb vp tv ta ke kbr ta hb weq hb hb hb hb vp tv hb vq tv tan wan hb vp
      wv hb vq wv wov hb vp wv hb hb hb hb vp tv hb vq tv ta tan hb vp tv ta ke
      kbr wan hb vp wv hb vq wv hb vp tv ta ke kbr hb hb vp tv ta hb vp wv
      imval.1 weqi id oveq1 hb vp tv ta ke kbr hb hb vp tv ta hb vp wv imval.1
      weqi id oveq12 hb hb hb ta hb vq tv tan kbr ta ta tb tan kbr ke hb vq tv
      tb ke kbr hb weq hb hb hb ta hb vq tv tan wan imval.1 hb vq wv wov
      imval.1 hb hb hb ta hb vq tv tan hb vq tv tb ke kbr tb wan imval.1 hb vq
      wv hb vq tv tb ke kbr hb hb vq tv tb hb vq wv imval.2 weqi id oveq2 oveq1
      ovl eqtri $.

    $( Value of the disjunction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    orval $p |- T. |= [ [ A \/ B ] = ( ! \ x : bool .
      [ [ A ==> x : bool ] ==> [ [ B ==> x : bool ] ==> x : bool ] ] ) ] $=
      hb ta tb tor kbr ta tb hb vp hb vq tal hb vx hb vp tv hb vx tv tim kbr hb
      vq tv hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc kl kl kbr tal hb vx
      ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc kt
      hb hb hb ta tb tor wor imval.1 imval.2 wov hb hb hb ta tb tor kt hb vp hb
      vq tal hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv
      tim kbr tim kbr kl kc kl kl wor imval.1 imval.2 vx vp vq df-or oveq hb hb
      hb vp vq tal hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb
      vx tv tim kbr tim kbr kl kc tal hb vx ta hb vx tv tim kbr hb vq tv hb vx
      tv tim kbr hb vx tv tim kbr tim kbr kl kc tal hb vx ta hb vx tv tim kbr
      tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc ta tb hb hb ht hb tal
      hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim
      kbr tim kbr kl hb wal hb hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx
      tv tim kbr hb vx tv tim kbr tim kbr hb hb hb hb vp tv hb vx tv tim kbr hb
      vq tv hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb hb vp tv hb vx
      tv tim wim hb vp wv hb vx wv wov hb hb hb hb vq tv hb vx tv tim kbr hb vx
      tv tim wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov hb vx
      wv wov wov wl wc imval.1 imval.2 hb hb ht hb hb vx hb vp tv hb vx tv tim
      kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim kbr kl hb vx ta hb vx
      tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim kbr kl tal hb
      vp tv ta ke kbr hb wal hb hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx
      tv tim kbr hb vx tv tim kbr tim kbr hb hb hb hb vp tv hb vx tv tim kbr hb
      vq tv hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb hb vp tv hb vx
      tv tim wim hb vp wv hb vx wv wov hb hb hb hb vq tv hb vx tv tim kbr hb vx
      tv tim wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov hb vx
      wv wov wov wl hb hb vx hb vp tv hb vx tv tim kbr hb vq tv hb vx tv tim
      kbr hb vx tv tim kbr tim kbr ta hb vx tv tim kbr hb vq tv hb vx tv tim
      kbr hb vx tv tim kbr tim kbr hb vp tv ta ke kbr hb hb hb hb vp tv hb vx
      tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb hb
      vp tv hb vx tv tim wim hb vp wv hb vx wv wov hb hb hb hb vq tv hb vx tv
      tim kbr hb vx tv tim wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb
      vx wv wov hb vx wv wov wov hb hb hb hb vp tv hb vx tv tim kbr hb vq tv hb
      vx tv tim kbr hb vx tv tim kbr ta hb vx tv tim kbr tim hb vp tv ta ke kbr
      wim hb hb hb hb vp tv hb vx tv tim wim hb vp wv hb vx wv wov hb hb hb hb
      vq tv hb vx tv tim kbr hb vx tv tim wim hb hb hb hb vq tv hb vx tv tim
      wim hb vq wv hb vx wv wov hb vx wv wov hb hb hb hb vp tv hb vx tv ta tim
      hb vp tv ta ke kbr wim hb vp wv hb vx wv hb vp tv ta ke kbr hb hb vp tv
      ta hb vp wv imval.1 weqi id oveq1 oveq1 leq ceq2 hb hb ht hb hb vx ta hb
      vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim kbr kl hb vx
      ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl tal
      hb vq tv tb ke kbr hb wal hb hb vx ta hb vx tv tim kbr hb vq tv hb vx tv
      tim kbr hb vx tv tim kbr tim kbr hb hb hb ta hb vx tv tim kbr hb vq tv hb
      vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb ta hb vx tv tim wim
      imval.1 hb vx wv wov hb hb hb hb vq tv hb vx tv tim kbr hb vx tv tim wim
      hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov hb vx wv wov wov
      wl hb hb vx ta hb vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim
      kbr tim kbr ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim
      kbr hb vq tv tb ke kbr hb hb hb ta hb vx tv tim kbr hb vq tv hb vx tv tim
      kbr hb vx tv tim kbr tim wim hb hb hb ta hb vx tv tim wim imval.1 hb vx
      wv wov hb hb hb hb vq tv hb vx tv tim kbr hb vx tv tim wim hb hb hb hb vq
      tv hb vx tv tim wim hb vq wv hb vx wv wov hb vx wv wov wov hb hb hb ta hb
      vx tv tim kbr hb vq tv hb vx tv tim kbr hb vx tv tim kbr tim hb vq tv tb
      ke kbr tb hb vx tv tim kbr hb vx tv tim kbr wim hb hb hb ta hb vx tv tim
      wim imval.1 hb vx wv wov hb hb hb hb vq tv hb vx tv tim kbr hb vx tv tim
      wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov hb vx wv wov
      hb hb hb hb vq tv hb vx tv tim kbr hb vx tv tb hb vx tv tim kbr tim hb vq
      tv tb ke kbr wim hb hb hb hb vq tv hb vx tv tim wim hb vq wv hb vx wv wov
      hb vx wv hb hb hb hb vq tv hb vx tv tb tim hb vq tv tb ke kbr wim hb vq
      wv hb vx wv hb vq tv tb ke kbr hb hb vq tv tb hb vq wv imval.2 weqi id
      oveq1 oveq1 oveq2 leq ceq2 ovl eqtri $.

    $( Value of the conjunction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    anval $p |- T. |= [ [ A /\ B ] = [ \ f : ( bool -> ( bool -> bool ) ) .
      [ A f : ( bool -> ( bool -> bool ) ) B ] =
        \ f : ( bool -> ( bool -> bool ) ) .
          [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $=
      hb ta tb tan kbr ta tb hb vp hb vq hb hb hb ht ht vf hb vp tv hb vq tv hb
      hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr
      kl ke kbr kl kl kbr hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl
      hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr kt hb hb hb ta
      tb tan wan imval.1 imval.2 wov hb hb hb ta tb tan kt hb vp hb vq hb hb hb
      ht ht vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf
      kt kt hb hb hb ht ht vf tv kbr kl ke kbr kl kl wan imval.1 imval.2 vf vp
      vq df-an oveq hb hb hb vp vq hb hb hb ht ht vf hb vp tv hb vq tv hb hb hb
      ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke
      kbr hb hb hb ht ht vf ta hb vq tv hb hb hb ht ht vf tv kbr kl hb hb hb ht
      ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr hb hb hb ht ht vf ta tb hb
      hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr
      kl ke kbr ta tb hb hb hb ht ht hb ht hb hb hb ht ht vf hb vp tv hb vq tv
      hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv
      kbr kl hb hb hb ht ht hb vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr hb
      hb hb hb vp tv hb vq tv hb hb hb ht ht vf tv hb hb hb ht ht vf wv hb vp
      wv hb vq wv wov wl hb hb hb ht ht hb vf kt kt hb hb hb ht ht vf tv kbr hb
      hb hb kt kt hb hb hb ht ht vf tv hb hb hb ht ht vf wv wtru wtru wov wl
      weqi imval.1 imval.2 hb hb hb ht ht hb ht hb hb hb ht ht hb ht hb hb hb
      hb ht ht vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr kl hb hb hb ht ht
      vf kt kt hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf ta hb vq tv hb hb
      hb ht ht vf tv kbr kl ke hb vp tv ta ke kbr hb hb hb ht ht hb ht weq hb
      hb hb ht ht hb vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr hb hb hb hb
      vp tv hb vq tv hb hb hb ht ht vf tv hb hb hb ht ht vf wv hb vp wv hb vq
      wv wov wl hb hb hb ht ht hb vf kt kt hb hb hb ht ht vf tv kbr hb hb hb kt
      kt hb hb hb ht ht vf tv hb hb hb ht ht vf wv wtru wtru wov wl hb hb hb ht
      ht hb vf hb vp tv hb vq tv hb hb hb ht ht vf tv kbr ta hb vq tv hb hb hb
      ht ht vf tv kbr hb vp tv ta ke kbr hb hb hb hb vp tv hb vq tv hb hb hb ht
      ht vf tv hb hb hb ht ht vf wv hb vp wv hb vq wv wov hb hb hb hb vp tv hb
      vq tv ta hb hb hb ht ht vf tv hb vp tv ta ke kbr hb hb hb ht ht vf wv hb
      vp wv hb vq wv hb vp tv ta ke kbr hb hb vp tv ta hb vp wv imval.1 weqi id
      oveq1 leq oveq1 hb hb hb ht ht hb ht hb hb hb ht ht hb ht hb hb hb hb ht
      ht vf ta hb vq tv hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb
      hb hb ht ht vf tv kbr kl hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr
      kl ke hb vq tv tb ke kbr hb hb hb ht ht hb ht weq hb hb hb ht ht hb vf ta
      hb vq tv hb hb hb ht ht vf tv kbr hb hb hb ta hb vq tv hb hb hb ht ht vf
      tv hb hb hb ht ht vf wv imval.1 hb vq wv wov wl hb hb hb ht ht hb vf kt
      kt hb hb hb ht ht vf tv kbr hb hb hb kt kt hb hb hb ht ht vf tv hb hb hb
      ht ht vf wv wtru wtru wov wl hb hb hb ht ht hb vf ta hb vq tv hb hb hb ht
      ht vf tv kbr ta tb hb hb hb ht ht vf tv kbr hb vq tv tb ke kbr hb hb hb
      ta hb vq tv hb hb hb ht ht vf tv hb hb hb ht ht vf wv imval.1 hb vq wv
      wov hb hb hb ta hb vq tv hb hb hb ht ht vf tv hb vq tv tb ke kbr tb hb hb
      hb ht ht vf wv imval.1 hb vq wv hb vq tv tb ke kbr hb hb vq tv tb hb vq
      wv imval.2 weqi id oveq2 leq oveq1 ovl eqtri $.
  $}

  ${
    $d p F $.  $d p al $.
    ax4g.1 $e |- F : ( al -> bool ) $.
    ax4g.2 $e |- A : al $.
    $( If ` F ` is true for all ` x : al ` , then it is true for ` A ` .
       (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ax4g $p |- ( ! F ) |= ( F A ) $=
      kt tf ta kc tal tf kc tal tf kc hal hb ht hb tal tf hal wal ax4g.1 wc
      trud hb tf ta kc hal vp kt kl ta kc kt tal tf kc hal hb tf ta ax4g.1
      ax4g.2 wc hal hb ta tf tal tf kc hal vp kt kl ax4g.1 ax4g.2 tal tf kc tf
      hal vp kt kl ke kbr tal tf kc tal tf kc kt tal tf kc tal tf kc hal hb ht
      hb tal tf hal wal ax4g.1 wc trud ax-cb1 id tal tf kc tf hal vp kt kl ke
      kbr ke kbr tal tf kc kt tal tf kc tal tf kc hal hb ht hb tal tf hal wal
      ax4g.1 wc trud ax-cb1 hal vp tf ax4g.1 alval a1i mpbi ceq1 hal vp kt ta
      tal tf kc ax4g.2 tal tf kc hal hb ht hb tal tf hal wal ax4g.1 wc trud
      hbth eqtri mpbir $.
  $}

  ${
    ax4.1 $e |- A : bool $.
    $( If ` A ` is true for all ` x : al ` , then it is true for ` A ` .
       (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ax4 $p |- ( ! \ x : al . A ) |= A $=
      hal vx ta kl hal vx tv kc ta tal hal vx ta kl kc hal hal vx tv hal vx ta
      kl hal hb vx ta ax4.1 wl hal vx wv ax4g hal vx ta kl hal vx tv kc ta ke
      kbr tal hal vx ta kl kc hal vx ta kl hal vx tv kc tal hal vx ta kl kc hal
      hal vx tv hal vx ta kl hal hb vx ta ax4.1 wl hal vx wv ax4g ax-cb1 hal hb
      vx ta ax4.1 beta a1i mpbi $.
  $}

  ${
    $d x R $.  $d x al $.
    alrimiv.1 $e |- R |= A $.
    $( If one can prove ` R |= A ` where ` R ` does not contain ` x ` , then
       ` A ` is true for all ` x ` .  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    alrimiv $p |- R |= ( ! \ x : al . A ) $=
      hal vx ta kl hal vx kt kl ke kbr tal hal vx ta kl kc tr hal hb vx ta kt
      tr ta tr alrimiv.1 ax-cb2 hb kt ta tr wtru ta tr alrimiv.1 eqtru eqcomi
      leq tal hal vx ta kl kc hal vx ta kl hal vx kt kl ke kbr ke kbr tr ta tr
      alrimiv.1 ax-cb1 hal vx hal vx ta kl hal hb vx ta ta tr alrimiv.1 ax-cb2
      wl alval a1i mpbir $.
  $}

  ${
    $d x B $.  $d x C $.  $d x al $.
    cla4v.1 $e |- A : bool $.
    cla4v.2 $e |- B : al $.
    cla4v.3 $e |- [ x : al = B ] |= [ A = C ] $.
    $( If ` A ( x ) ` is true for all ` x : al ` , then it is true for
       ` C = A ( B ) ` .  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    cla4v $p |- ( ! \ x : al . A ) |= C $=
      hal vx ta kl tb kc tc tal hal vx ta kl kc hal tb hal vx ta kl hal hb vx
      ta cla4v.1 wl cla4v.2 ax4g hal vx ta kl tb kc tc ke kbr tal hal vx ta kl
      kc hal vx ta kl tb kc tal hal vx ta kl kc hal tb hal vx ta kl hal hb vx
      ta cla4v.1 wl cla4v.2 ax4g ax-cb1 hal hb vx ta tc tb cla4v.1 cla4v.2
      cla4v.3 cl a1i mpbi $.
  $}

  ${
    $d p A $.
    pm2.21.1 $e |- A : bool $.
    $( A falsehood implies anything.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    pm2.21 $p |- F. |= A $=
      tfal tal hb vp hb vp tv kl kc ta tfal tal hb vp hb vp tv kl kc tfal tfal
      wfal id tfal tal hb vp hb vp tv kl kc ke kbr tfal wfal vp df-fal a1i mpbi
      hb vp hb vp tv ta ta hb vp wv pm2.21.1 hb vp tv ta ke kbr hb hb vp tv ta
      hb vp wv pm2.21.1 weqi id cla4v syl $.
  $}

  ${
    $d f x y A $.  $d f x y B $.
    dfan2.1 $e |- A : bool $.
    dfan2.2 $e |- B : bool $.
    $( An alternative definition of the "and" term in terms of the context
       conjunction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    dfan2 $p |- T. |= [ [ A /\ B ] = ( A , B ) ] $=
      ta tb tan kbr ta tb kct ta tb tan kbr ta tb kt ta ta tb tan kbr ta tb tan
      kbr hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov trud hb hb hb hb ht ht vf
      ta tb hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vx tv kl kl kc hb hb hb
      ht ht vf kt kt hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vx tv kl kl kc
      ta tb tan kbr ta kt hb hb hb ht ht hb hb hb hb ht ht vf ta tb hb hb hb ht
      ht vf tv kbr kl hb vx hb vy hb vx tv kl kl hb hb hb ht ht hb vf ta tb hb
      hb hb ht ht vf tv kbr hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht
      vf wv dfan2.1 dfan2.2 wov wl hb hb hb ht vx hb vy hb vx tv kl hb hb vy hb
      vx tv hb vx wv wl wl wc hb hb hb ht ht hb hb vx hb vy hb vx tv kl kl hb
      hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl ta tb tan kbr hb hb hb
      ht ht vf kt kt hb hb hb ht ht vf tv kbr kl hb hb hb ht ht hb vf ta tb hb
      hb hb ht ht vf tv kbr hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht
      vf wv dfan2.1 dfan2.2 wov wl hb hb hb ht vx hb vy hb vx tv kl hb hb vy hb
      vx tv hb vx wv wl wl ta tb tan kbr hb hb hb ht ht vf ta tb hb hb hb ht ht
      vf tv kbr kl hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr
      ta tb tan kbr ta tb tan kbr hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov id
      ta tb tan kbr hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb hb
      hb ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr ke kbr ta tb tan kbr
      hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov vf ta tb dfan2.1 dfan2.2 anval
      a1i mpbi ceq1 hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb vx
      hb vy hb vx tv kl kl kc ta ke kbr ta tb tan kbr hb hb hb ta tb tan wan
      dfan2.1 dfan2.2 wov hb hb hb ht ht hb vf ta tb hb hb hb ht ht vf tv kbr
      ta hb vx hb vy hb vx tv kl kl hb hb hb ta tb hb hb hb ht ht vf tv hb hb
      hb ht ht vf wv dfan2.1 dfan2.2 wov hb hb hb ht vx hb vy hb vx tv kl hb hb
      vy hb vx tv hb vx wv wl wl hb ta tb hb hb hb ht ht vf tv kbr ta tb hb vx
      hb vy hb vx tv kl kl kbr ta hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl
      kl ke kbr hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht vf wv
      dfan2.1 dfan2.2 wov hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht vf
      tv hb vx hb vy hb vx tv kl kl ke kbr hb vx hb vy hb vx tv kl kl hb hb hb
      ht ht vf wv dfan2.1 dfan2.2 hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl
      kl ke kbr hb hb hb ht ht hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl
      hb hb hb ht ht vf wv hb hb hb ht vx hb vy hb vx tv kl hb hb vy hb vx tv
      hb vx wv wl wl weqi id oveq ta tb hb vx hb vy hb vx tv kl kl kbr ta ke
      kbr hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl ke kbr hb hb hb ht ht
      hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl hb hb hb ht ht vf wv hb
      hb hb ht vx hb vy hb vx tv kl hb hb vy hb vx tv hb vx wv wl wl weqi hb hb
      hb vx vy hb vx tv ta ta ta tb hb vx wv dfan2.1 dfan2.2 hb vx tv ta ke kbr
      hb hb vx tv ta hb vx wv dfan2.1 weqi id hb ta hb vy tv tb ke kbr hb hb vy
      tv tb hb vy wv dfan2.2 weqi dfan2.1 eqid ovl a1i eqtri cl a1i hb hb hb ht
      ht vf kt kt hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vx tv kl kl kc kt
      ke kbr ta tb tan kbr hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov hb hb hb
      ht ht hb vf kt kt hb hb hb ht ht vf tv kbr kt hb vx hb vy hb vx tv kl kl
      hb hb hb kt kt hb hb hb ht ht vf tv hb hb hb ht ht vf wv wtru wtru wov hb
      hb hb ht vx hb vy hb vx tv kl hb hb vy hb vx tv hb vx wv wl wl hb kt kt
      hb hb hb ht ht vf tv kbr kt kt hb vx hb vy hb vx tv kl kl kbr kt hb hb hb
      ht ht vf tv hb vx hb vy hb vx tv kl kl ke kbr hb hb hb kt kt hb hb hb ht
      ht vf tv hb hb hb ht ht vf wv wtru wtru wov hb hb hb kt kt hb hb hb ht ht
      vf tv hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl ke kbr hb vx hb vy
      hb vx tv kl kl hb hb hb ht ht vf wv wtru wtru hb hb hb ht ht vf tv hb vx
      hb vy hb vx tv kl kl ke kbr hb hb hb ht ht hb hb hb ht ht vf tv hb vx hb
      vy hb vx tv kl kl hb hb hb ht ht vf wv hb hb hb ht vx hb vy hb vx tv kl
      hb hb vy hb vx tv hb vx wv wl wl weqi id oveq kt kt hb vx hb vy hb vx tv
      kl kl kbr kt ke kbr hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl ke
      kbr hb hb hb ht ht hb hb hb ht ht vf tv hb vx hb vy hb vx tv kl kl hb hb
      hb ht ht vf wv hb hb hb ht vx hb vy hb vx tv kl hb hb vy hb vx tv hb vx
      wv wl wl weqi hb hb hb vx vy hb vx tv kt kt kt kt hb vx wv wtru wtru hb
      vx tv kt ke kbr hb hb vx tv kt hb vx wv wtru weqi id hb kt hb vy tv kt ke
      kbr hb hb vy tv kt hb vy wv wtru weqi wtru eqid ovl a1i eqtri cl a1i
      3eqtr3i mpbir kt tb ta tb tan kbr ta tb tan kbr hb hb hb ta tb tan wan
      dfan2.1 dfan2.2 wov trud hb hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv
      kbr kl hb vx hb vy hb vy tv kl kl kc hb hb hb ht ht vf kt kt hb hb hb ht
      ht vf tv kbr kl hb vx hb vy hb vy tv kl kl kc ta tb tan kbr tb kt hb hb
      hb ht ht hb hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb vx hb
      vy hb vy tv kl kl hb hb hb ht ht hb vf ta tb hb hb hb ht ht vf tv kbr hb
      hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht vf wv dfan2.1 dfan2.2 wov
      wl hb hb hb ht vx hb vy hb vy tv kl hb hb vy hb vy tv hb vy wv wl wl wc
      hb hb hb ht ht hb hb vx hb vy hb vy tv kl kl hb hb hb ht ht vf ta tb hb
      hb hb ht ht vf tv kbr kl ta tb tan kbr hb hb hb ht ht vf kt kt hb hb hb
      ht ht vf tv kbr kl hb hb hb ht ht hb vf ta tb hb hb hb ht ht vf tv kbr hb
      hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht vf wv dfan2.1 dfan2.2 wov
      wl hb hb hb ht vx hb vy hb vy tv kl hb hb vy hb vy tv hb vy wv wl wl ta
      tb tan kbr hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb hb hb
      ht ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr ta tb tan kbr ta tb tan
      kbr hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov id ta tb tan kbr hb hb hb
      ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt hb hb
      hb ht ht vf tv kbr kl ke kbr ke kbr ta tb tan kbr hb hb hb ta tb tan wan
      dfan2.1 dfan2.2 wov vf ta tb dfan2.1 dfan2.2 anval a1i mpbi ceq1 hb hb hb
      ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vy tv kl kl kc
      tb ke kbr ta tb tan kbr hb hb hb ta tb tan wan dfan2.1 dfan2.2 wov hb hb
      hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vy tv kl
      kl kc ta tb hb vx hb vy hb vy tv kl kl kbr tb kt hb hb hb ht ht hb hb hb
      hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb vx hb vy hb vy tv kl kl
      hb hb hb ht ht hb vf ta tb hb hb hb ht ht vf tv kbr hb hb hb ta tb hb hb
      hb ht ht vf tv hb hb hb ht ht vf wv dfan2.1 dfan2.2 wov wl hb hb hb ht vx
      hb vy hb vy tv kl hb hb vy hb vy tv hb vy wv wl wl wc hb hb hb ht ht hb
      vf ta tb hb hb hb ht ht vf tv kbr ta tb hb vx hb vy hb vy tv kl kl kbr hb
      vx hb vy hb vy tv kl kl hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht
      ht vf wv dfan2.1 dfan2.2 wov hb hb hb ht vx hb vy hb vy tv kl hb hb vy hb
      vy tv hb vy wv wl wl hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht
      vf tv hb vx hb vy hb vy tv kl kl ke kbr hb vx hb vy hb vy tv kl kl hb hb
      hb ht ht vf wv dfan2.1 dfan2.2 hb hb hb ht ht vf tv hb vx hb vy hb vy tv
      kl kl ke kbr hb hb hb ht ht hb hb hb ht ht vf tv hb vx hb vy hb vy tv kl
      kl hb hb hb ht ht vf wv hb hb hb ht vx hb vy hb vy tv kl hb hb vy hb vy
      tv hb vy wv wl wl weqi id oveq cl ta tb hb vx hb vy hb vy tv kl kl kbr tb
      ke kbr kt wtru hb hb hb vx vy hb vy tv hb vy tv tb ta tb hb vy wv dfan2.1
      dfan2.2 hb hb vy tv hb vx tv ta ke kbr hb hb vx tv ta hb vx wv dfan2.1
      weqi hb vy wv eqid hb vy tv tb ke kbr hb hb vy tv tb hb vy wv dfan2.2
      weqi id ovl a1i eqtri a1i hb hb hb ht ht vf kt kt hb hb hb ht ht vf tv
      kbr kl hb vx hb vy hb vy tv kl kl kc kt ke kbr ta tb tan kbr hb hb hb ta
      tb tan wan dfan2.1 dfan2.2 wov hb hb hb ht ht hb vf kt kt hb hb hb ht ht
      vf tv kbr kt hb vx hb vy hb vy tv kl kl hb hb hb kt kt hb hb hb ht ht vf
      tv hb hb hb ht ht vf wv wtru wtru wov hb hb hb ht vx hb vy hb vy tv kl hb
      hb vy hb vy tv hb vy wv wl wl hb kt kt hb hb hb ht ht vf tv kbr kt kt hb
      vx hb vy hb vy tv kl kl kbr kt hb hb hb ht ht vf tv hb vx hb vy hb vy tv
      kl kl ke kbr hb hb hb kt kt hb hb hb ht ht vf tv hb hb hb ht ht vf wv
      wtru wtru wov hb hb hb kt kt hb hb hb ht ht vf tv hb hb hb ht ht vf tv hb
      vx hb vy hb vy tv kl kl ke kbr hb vx hb vy hb vy tv kl kl hb hb hb ht ht
      vf wv wtru wtru hb hb hb ht ht vf tv hb vx hb vy hb vy tv kl kl ke kbr hb
      hb hb ht ht hb hb hb ht ht vf tv hb vx hb vy hb vy tv kl kl hb hb hb ht
      ht vf wv hb hb hb ht vx hb vy hb vy tv kl hb hb vy hb vy tv hb vy wv wl
      wl weqi id oveq kt kt hb vx hb vy hb vy tv kl kl kbr kt ke kbr hb hb hb
      ht ht vf tv hb vx hb vy hb vy tv kl kl ke kbr hb hb hb ht ht hb hb hb ht
      ht vf tv hb vx hb vy hb vy tv kl kl hb hb hb ht ht vf wv hb hb hb ht vx
      hb vy hb vy tv kl hb hb vy hb vy tv hb vy wv wl wl weqi hb hb hb vx vy hb
      vy tv hb vy tv kt kt kt hb vy wv wtru wtru hb hb vy tv hb vx tv kt ke kbr
      hb hb vx tv kt hb vx wv wtru weqi hb vy wv eqid hb vy tv kt ke kbr hb hb
      vy tv kt hb vy wv wtru weqi id ovl a1i eqtri cl a1i 3eqtr3i mpbir jca hb
      hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb hb hb ht ht vf kt kt
      hb hb hb ht ht vf tv kbr kl ke kbr ta tb tan kbr ta tb kct hb hb hb ht ht
      hb vf ta tb hb hb hb ht ht vf tv kbr kt kt hb hb hb ht ht vf tv kbr ta tb
      kct hb hb hb ta tb hb hb hb ht ht vf tv hb hb hb ht ht vf wv dfan2.1
      dfan2.2 wov hb kt kt hb hb hb ht ht vf tv kbr ta tb hb hb hb ht ht vf tv
      kbr ta tb kct hb hb hb kt kt hb hb hb ht ht vf tv hb hb hb ht ht vf wv
      wtru wtru wov hb hb hb kt kt ta hb hb hb ht ht vf tv ta tb kct tb hb hb
      hb ht ht vf wv wtru wtru ta ta tb kct ta tb dfan2.1 dfan2.2 simpl eqtru
      tb ta tb kct ta tb dfan2.1 dfan2.2 simpr eqtru oveq12 eqcomi leq ta tb
      tan kbr hb hb hb ht ht vf ta tb hb hb hb ht ht vf tv kbr kl hb hb hb ht
      ht vf kt kt hb hb hb ht ht vf tv kbr kl ke kbr ke kbr ta tb kct ta ta tb
      kct ta tb dfan2.1 dfan2.2 simpl ax-cb1 vf ta tb dfan2.1 dfan2.2 anval a1i
      mpbir dedi $.
  $}

  ${
    hbct.1 $e |- A : bool $.
    hbct.2 $e |- B : al $.
    hbct.3 $e |- C : bool $.
    hbct.4 $e |- R |= [ ( \ x : al . A B ) = A ] $.
    hbct.5 $e |- R |= [ ( \ x : al . C B ) = C ] $.
    $( Hypothesis builder for context conjunction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    hbct $p |- R |= [ ( \ x : al . ( A , C ) B ) = ( A , C ) ] $=
      tr kt hal vx ta tc kct kl tb kc ta tc kct ke kbr tr hal vx ta kl tb kc ta
      ke kbr tr hbct.4 ax-cb1 trud hal hb vx ta tc tan kbr tb kt tr ta tc kct
      ta tc hbct.1 hbct.3 wct hbct.2 hb ta tc tan kbr ta tc kct kt hb hb hb ta
      tc tan wan hbct.1 hbct.3 wov ta tc hbct.1 hbct.3 dfan2 eqcomi tr kt hal
      vx ta tc tan kbr kl tb kc ta tc tan kbr ke kbr hal hb hb hb vx ta tb tc
      tan tr wan hbct.1 hbct.2 hbct.3 hal hb hb hb ht ht vx tan tb tr wan
      hbct.2 hal vx ta kl tb kc ta ke kbr tr hbct.4 ax-cb1 a17i hbct.4 hbct.5
      hbov wtru adantr hbxfrf mpdan $.
  $}

  ${
    mp.1 $e |- T : bool $.
    mp.2 $e |- R |= S $.
    mp.3 $e |- R |= [ S ==> T ] $.
    $( Modus ponens.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    mpd $p |- R |= T $=
      tr ts tt ts tt tan kbr ts tt kct tr ts ts tt tan kbr tr mp.2 ts tt tim
      kbr ts tt tan kbr ts ke kbr tr mp.3 ts tt tim kbr ts tt tan kbr ts ke kbr
      ke kbr tr ts tr mp.2 ax-cb1 ts tt ts tr mp.2 ax-cb2 mp.1 imval a1i mpbi
      mpbir ts tt tan kbr ts tt kct ke kbr tr ts tr mp.2 ax-cb1 ts tt ts tr
      mp.2 ax-cb2 mp.1 dfan2 a1i mpbi simprd $.
  $}

  ${
    imp.1 $e |- S : bool $.
    imp.2 $e |- T : bool $.
    imp.3 $e |- R |= [ S ==> T ] $.
    $( Importation deduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    imp $p |- ( R , S ) |= T $=
      tr ts kct ts tt imp.2 tr ts ts tt tim kbr tr imp.3 ax-cb1 imp.1 simpr tr
      ts ts tt tim kbr imp.3 imp.1 adantr mpd $.
  $}

  ${
    ex.1 $e |- ( R , S ) |= T $.
    $( Exportation deduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ex $p |- R |= [ S ==> T ] $=
      ts tt tan kbr ts ke kbr ts tt tim kbr tr hb ts tt tan kbr ts tt kct ts tr
      hb hb hb ts tt tan wan tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts kct
      ex.1 ax-cb2 wov ts tt tan kbr ts tt kct ke kbr tr tr ts tt tr ts kct ex.1
      ax-cb1 wctl ts tt tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts kct ex.1
      ax-cb2 dfan2 a1i tr ts tt kct ts tr ts tt kct kct ts tt tr ts tt kct tr
      ts tt tr ts kct ex.1 ax-cb1 wctl ts tt tr ts tt tr ts kct ex.1 ax-cb1
      wctr tt tr ts kct ex.1 ax-cb2 wct simpr simpld tr ts kct ts tt tr ts tr
      ts tt tr ts kct ex.1 ax-cb1 wctl tr ts tt tr ts kct ex.1 ax-cb1 wctr
      simpr ex.1 jca ded eqtri ts tt tim kbr ts tt tan kbr ts ke kbr ke kbr tr
      ts tt tan kbr ts ke kbr tr hb ts tt tan kbr ts tt kct ts tr hb hb hb ts
      tt tan wan tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts kct ex.1 ax-cb2
      wov ts tt tan kbr ts tt kct ke kbr tr tr ts tt tr ts kct ex.1 ax-cb1 wctl
      ts tt tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts kct ex.1 ax-cb2 dfan2
      a1i tr ts tt kct ts tr ts tt kct kct ts tt tr ts tt kct tr ts tt tr ts
      kct ex.1 ax-cb1 wctl ts tt tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts
      kct ex.1 ax-cb2 wct simpr simpld tr ts kct ts tt tr ts tr ts tt tr ts kct
      ex.1 ax-cb1 wctl tr ts tt tr ts kct ex.1 ax-cb1 wctr simpr ex.1 jca ded
      eqtri ax-cb1 ts tt tr ts tt tr ts kct ex.1 ax-cb1 wctr tt tr ts kct ex.1
      ax-cb2 imval a1i mpbir $.
  $}

  ${
    notval2.1 $e |- A : bool $.
    $( Another way two write ` ~ A ` , the negation of ` A ` .  (Contributed by
       Mario Carneiro, 9-Oct-2014.) $)
    notval2 $p |- T. |= [ ( ~ A ) = [ A = F. ] ] $=
      hb tne ta kc ta tfal tim kbr ta tfal ke kbr kt hb hb tne ta wnot
      notval2.1 wc ta notval2.1 notval ta tfal tim kbr ta tfal ke kbr ta tfal
      tim kbr ta tfal ta tfal tim kbr ta kct ta tfal wfal ta tfal tim kbr ta hb
      hb hb ta tfal tim wim notval2.1 wfal wov notval2.1 simpr ta tfal tim kbr
      ta hb hb hb ta tfal tim wim notval2.1 wfal wov notval2.1 simpl mpd tfal
      ta tfal tim kbr ta ta notval2.1 pm2.21 hb hb hb ta tfal tim wim notval2.1
      wfal wov adantl ded ta tfal ke kbr ta tfal ta tfal ta tfal ke kbr ta kct
      ta tfal ke kbr ta ta tfal ke kbr ta tfal tim kbr ta tfal tim kbr ta tfal
      ta tfal tim kbr ta kct ta tfal wfal ta tfal tim kbr ta hb hb hb ta tfal
      tim wim notval2.1 wfal wov notval2.1 simpr ta tfal tim kbr ta hb hb hb ta
      tfal tim wim notval2.1 wfal wov notval2.1 simpl mpd tfal ta tfal tim kbr
      ta ta notval2.1 pm2.21 hb hb hb ta tfal tim wim notval2.1 wfal wov adantl
      ded ax-cb2 notval2.1 simpr ta tfal ke kbr ta ta tfal ke kbr ta tfal tim
      kbr ta tfal tim kbr ta tfal ta tfal tim kbr ta kct ta tfal wfal ta tfal
      tim kbr ta hb hb hb ta tfal tim wim notval2.1 wfal wov notval2.1 simpr ta
      tfal tim kbr ta hb hb hb ta tfal tim wim notval2.1 wfal wov notval2.1
      simpl mpd tfal ta tfal tim kbr ta ta notval2.1 pm2.21 hb hb hb ta tfal
      tim wim notval2.1 wfal wov adantl ded ax-cb2 notval2.1 simpl mpbi ex dedi
      eqtri $.

    $( One side of ~ notnot .  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    notnot1 $p |- A |= ( ~ ( ~ A ) ) $=
      tne ta kc tfal tim kbr tne tne ta kc kc ta ta tne ta kc tfal ta tne ta kc
      kct ta tfal wfal ta tne ta kc notval2.1 hb hb tne ta wnot notval2.1 wc
      simpl tne ta kc ta tfal tim kbr ta tne ta kc kct ta tne ta kc notval2.1
      hb hb tne ta wnot notval2.1 wc simpr tne ta kc ta tfal tim kbr ke kbr ta
      tne ta kc kct ta ta tne ta kc kct ta tne ta kc notval2.1 hb hb tne ta
      wnot notval2.1 wc simpl ax-cb1 ta notval2.1 notval a1i mpbi mpd ex tne
      tne ta kc kc tne ta kc tfal tim kbr ke kbr ta notval2.1 tne ta kc hb hb
      tne ta wnot notval2.1 wc notval a1i mpbir $.
  $}

  ${
    con2d.1 $e |- T : bool $.
    con2d.2 $e |- ( R , S ) |= ( ~ T ) $.
    $( A contraposition deduction.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    con2d $p |- ( R , T ) |= ( ~ S ) $=
      ts tfal tim kbr tne ts kc tr tt kct tr tt kct ts tfal tfal tr ts tt tr ts
      kct tt tfal con2d.1 wfal tne tt kc tt tfal tim kbr tr ts kct con2d.2 tne
      tt kc tt tfal tim kbr ke kbr tr ts kct tne tt kc tr ts kct con2d.2 ax-cb1
      tt con2d.1 notval a1i mpbi imp an32s ex tne ts kc ts tfal tim kbr ke kbr
      tr tt kct tr tt tr ts tne tt kc tr ts kct con2d.2 ax-cb1 wctl con2d.1 wct
      ts tr ts tne tt kc tr ts kct con2d.2 ax-cb1 wctr notval a1i mpbir $.
  $}

  ${
    con3d.1 $e |- ( R , S ) |= T $.
    $( A contraposition deduction.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    con3d $p |- ( R , ( ~ T ) ) |= ( ~ S ) $=
      tr ts tne tt kc hb hb tne tt wnot tt tr ts kct con3d.1 ax-cb2 wc tr ts
      kct tt tne tne tt kc kc con3d.1 tt tt tr ts kct con3d.1 ax-cb2 notnot1
      syl con2d $.
  $}

  ${
    $d x A $.  $d x B $.  $d x T $.
    ecase.1 $e |- A : bool $.
    ecase.2 $e |- B : bool $.
    ecase.3 $e |- T : bool $.
    ecase.4 $e |- R |= [ A \/ B ] $.
    ecase.5 $e |- ( R , A ) |= T $.
    ecase.6 $e |- ( R , B ) |= T $.
    $( Elimination by cases.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    ecase $p |- R |= T $=
      tr tb tt tim kbr tt ecase.3 tr tb tt ecase.6 ex tr ta tt tim kbr tb tt
      tim kbr tt tim kbr hb hb hb tb tt tim kbr tt tim wim hb hb hb tb tt tim
      wim ecase.2 ecase.3 wov ecase.3 wov tr ta tt ecase.5 ex tr tal hb vx ta
      hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc ta tt
      tim kbr tb tt tim kbr tt tim kbr tim kbr ta tb tor kbr tal hb vx ta hb vx
      tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc tr ecase.4
      ta tb tor kbr tal hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv
      tim kbr tim kbr kl kc ke kbr tr ta tb tor kbr tr ecase.4 ax-cb1 vx ta tb
      ecase.1 ecase.2 orval a1i mpbi hb vx ta hb vx tv tim kbr tb hb vx tv tim
      kbr hb vx tv tim kbr tim kbr tt ta tt tim kbr tb tt tim kbr tt tim kbr
      tim kbr hb hb hb ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr
      tim wim hb hb hb ta hb vx tv tim wim ecase.1 hb vx wv wov hb hb hb tb hb
      vx tv tim kbr hb vx tv tim wim hb hb hb tb hb vx tv tim wim ecase.2 hb vx
      wv wov hb vx wv wov wov ecase.3 hb hb hb ta hb vx tv tim kbr tb hb vx tv
      tim kbr hb vx tv tim kbr ta tt tim kbr tim hb vx tv tt ke kbr tb tt tim
      kbr tt tim kbr wim hb hb hb ta hb vx tv tim wim ecase.1 hb vx wv wov hb
      hb hb tb hb vx tv tim kbr hb vx tv tim wim hb hb hb tb hb vx tv tim wim
      ecase.2 hb vx wv wov hb vx wv wov hb hb hb ta hb vx tv tim hb vx tv tt ke
      kbr tt wim ecase.1 hb vx wv hb vx tv tt ke kbr hb hb vx tv tt hb vx wv
      ecase.3 weqi id oveq2 hb hb hb tb hb vx tv tim kbr hb vx tv tb tt tim kbr
      tim hb vx tv tt ke kbr tt wim hb hb hb tb hb vx tv tim wim ecase.2 hb vx
      wv wov hb vx wv hb hb hb tb hb vx tv tim hb vx tv tt ke kbr tt wim
      ecase.2 hb vx wv hb vx tv tt ke kbr hb hb vx tv tt hb vx wv ecase.3 weqi
      id oveq2 hb vx tv tt ke kbr hb hb vx tv tt hb vx wv ecase.3 weqi id
      oveq12 oveq12 cla4v syl mpd mpd $.
  $}

  ${
    $d x A $.  $d x B $.
    olc.1 $e |- A : bool $.
    olc.2 $e |- B : bool $.
    $( Or introduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    olc $p |- B |= [ A \/ B ] $=
      hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl
      hb vx kt kl ke kbr ta tb tor kbr tb hb hb vx ta hb vx tv tim kbr tb hb vx
      tv tim kbr hb vx tv tim kbr tim kbr kt tb hb hb hb ta hb vx tv tim kbr tb
      hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb ta hb vx tv tim wim
      olc.1 hb vx wv wov hb hb hb tb hb vx tv tim kbr hb vx tv tim wim hb hb hb
      tb hb vx tv tim wim olc.2 hb vx wv wov hb vx wv wov wov hb kt ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr tb wtru ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr tb tb ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tb ta hb vx tv tim kbr tb hb
      vx tv tim kbr hb vx tv tim kbr tb tb hb vx tv tim kbr hb vx tv tb tb hb
      vx tv tim kbr kct tb hb vx tv hb vx wv tb tb hb vx tv tim kbr olc.2 hb hb
      hb tb hb vx tv tim wim olc.2 hb vx wv wov simpl tb tb hb vx tv tim kbr
      olc.2 hb hb hb tb hb vx tv tim wim olc.2 hb vx wv wov simpr mpd ex hb hb
      hb ta hb vx tv tim wim olc.1 hb vx wv wov adantr ex eqtru eqcomi leq ta
      tb tor kbr hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr
      tim kbr kl hb vx kt kl ke kbr ke kbr tb olc.2 hb ta tb tor kbr tal hb vx
      ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl kc hb
      vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl hb
      vx kt kl ke kbr kt hb hb hb ta tb tor wor olc.1 olc.2 wov vx ta tb olc.1
      olc.2 orval hb vx hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv
      tim kbr tim kbr kl hb hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx
      tv tim kbr tim kbr hb hb hb ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx
      tv tim kbr tim wim hb hb hb ta hb vx tv tim wim olc.1 hb vx wv wov hb hb
      hb tb hb vx tv tim kbr hb vx tv tim wim hb hb hb tb hb vx tv tim wim
      olc.2 hb vx wv wov hb vx wv wov wov wl alval eqtri a1i mpbir $.

    $( Or introduction.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    orc $p |- A |= [ A \/ B ] $=
      hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr kl
      hb vx kt kl ke kbr ta tb tor kbr ta hb hb vx ta hb vx tv tim kbr tb hb vx
      tv tim kbr hb vx tv tim kbr tim kbr kt ta hb hb hb ta hb vx tv tim kbr tb
      hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb ta hb vx tv tim wim
      olc.1 hb vx wv wov hb hb hb tb hb vx tv tim kbr hb vx tv tim wim hb hb hb
      tb hb vx tv tim wim olc.2 hb vx wv wov hb vx wv wov wov hb kt ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr ta wtru ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr tim kbr ta ta ta hb vx tv
      tim kbr tb hb vx tv tim kbr hb vx tv tim kbr ta ta hb vx tv tim kbr kct
      tb hb vx tv tim kbr hb vx tv ta ta hb vx tv tim kbr kct tb hb vx tv tim
      kbr hb vx tv ta ta hb vx tv tim kbr kct ta hb vx tv hb vx wv ta ta hb vx
      tv tim kbr olc.1 hb hb hb ta hb vx tv tim wim olc.1 hb vx wv wov simpl ta
      ta hb vx tv tim kbr olc.1 hb hb hb ta hb vx tv tim wim olc.1 hb vx wv wov
      simpr mpd hb hb hb tb hb vx tv tim wim olc.2 hb vx wv wov adantr ex ex
      eqtru eqcomi leq ta tb tor kbr hb vx ta hb vx tv tim kbr tb hb vx tv tim
      kbr hb vx tv tim kbr tim kbr kl hb vx kt kl ke kbr ke kbr ta olc.1 hb ta
      tb tor kbr tal hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv tim
      kbr tim kbr kl kc hb vx ta hb vx tv tim kbr tb hb vx tv tim kbr hb vx tv
      tim kbr tim kbr kl hb vx kt kl ke kbr kt hb hb hb ta tb tor wor olc.1
      olc.2 wov vx ta tb olc.1 olc.2 orval hb vx hb vx ta hb vx tv tim kbr tb
      hb vx tv tim kbr hb vx tv tim kbr tim kbr kl hb hb vx ta hb vx tv tim kbr
      tb hb vx tv tim kbr hb vx tv tim kbr tim kbr hb hb hb ta hb vx tv tim kbr
      tb hb vx tv tim kbr hb vx tv tim kbr tim wim hb hb hb ta hb vx tv tim wim
      olc.1 hb vx wv wov hb hb hb tb hb vx tv tim kbr hb vx tv tim wim hb hb hb
      tb hb vx tv tim wim olc.2 hb vx wv wov hb vx wv wov wov wl alval eqtri
      a1i mpbir $.
  $}

  ${
    $d p x F $.  $d x R $.  $d p x T $.  $d p x al $.
    exlimdv2.1 $e |- F : ( al -> bool ) $.
    exlimdv2.2 $e |- ( R , ( F x : al ) ) |= T $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimdv2 $p |- ( R , ( ? F ) ) |= T $=
      tr tex tf kc kct tal hal vx tf hal vx tv kc tt tim kbr kl kc tt tt tr tf
      hal vx tv kc kct exlimdv2.2 ax-cb2 tr tex tf kc tal hal vx tf hal vx tv
      kc tt tim kbr kl kc hal vx tf hal vx tv kc tt tim kbr tr tr tf hal vx tv
      kc tt exlimdv2.2 ex alrimiv hal hb ht hb tex tf hal wex exlimdv2.1 wc
      adantr tr tex tf kc kct tal hb vp tal hal vx tf hal vx tv kc hb vp tv tim
      kbr kl kc hb vp tv tim kbr kl kc tal hal vx tf hal vx tv kc tt tim kbr kl
      kc tt tim kbr tex tf kc tal hb vp tal hal vx tf hal vx tv kc hb vp tv tim
      kbr kl kc hb vp tv tim kbr kl kc tr tex tf kc kct tr tex tf kc tr tf hal
      vx tv kc tt tr tf hal vx tv kc kct exlimdv2.2 ax-cb1 wctl hal hb ht hb
      tex tf hal wex exlimdv2.1 wc simpr tex tf kc tal hb vp tal hal vx tf hal
      vx tv kc hb vp tv tim kbr kl kc hb vp tv tim kbr kl kc ke kbr tr tex tf
      kc kct tr tex tf kc tr tf hal vx tv kc tt tr tf hal vx tv kc kct
      exlimdv2.2 ax-cb1 wctl hal hb ht hb tex tf hal wex exlimdv2.1 wc wct hal
      vx vp tf exlimdv2.1 exval a1i mpbi hb vp tal hal vx tf hal vx tv kc hb vp
      tv tim kbr kl kc hb vp tv tim kbr tt tal hal vx tf hal vx tv kc tt tim
      kbr kl kc tt tim kbr hb hb hb tal hal vx tf hal vx tv kc hb vp tv tim kbr
      kl kc hb vp tv tim wim hal hb ht hb tal hal vx tf hal vx tv kc hb vp tv
      tim kbr kl hal wal hal hb vx tf hal vx tv kc hb vp tv tim kbr hb hb hb tf
      hal vx tv kc hb vp tv tim wim hal hb tf hal vx tv exlimdv2.1 hal vx wv wc
      hb vp wv wov wl wc hb vp wv wov tt tr tf hal vx tv kc kct exlimdv2.2
      ax-cb2 hb hb hb tal hal vx tf hal vx tv kc hb vp tv tim kbr kl kc hb vp
      tv tal hal vx tf hal vx tv kc tt tim kbr kl kc tim hb vp tv tt ke kbr tt
      wim hal hb ht hb tal hal vx tf hal vx tv kc hb vp tv tim kbr kl hal wal
      hal hb vx tf hal vx tv kc hb vp tv tim kbr hb hb hb tf hal vx tv kc hb vp
      tv tim wim hal hb tf hal vx tv exlimdv2.1 hal vx wv wc hb vp wv wov wl wc
      hb vp wv hal hb ht hb hal vx tf hal vx tv kc hb vp tv tim kbr kl hal vx
      tf hal vx tv kc tt tim kbr kl tal hb vp tv tt ke kbr hal wal hal hb vx tf
      hal vx tv kc hb vp tv tim kbr hb hb hb tf hal vx tv kc hb vp tv tim wim
      hal hb tf hal vx tv exlimdv2.1 hal vx wv wc hb vp wv wov wl hal hb vx tf
      hal vx tv kc hb vp tv tim kbr tf hal vx tv kc tt tim kbr hb vp tv tt ke
      kbr hb hb hb tf hal vx tv kc hb vp tv tim wim hal hb tf hal vx tv
      exlimdv2.1 hal vx wv wc hb vp wv wov hb hb hb tf hal vx tv kc hb vp tv
      tim hb vp tv tt ke kbr tt wim hal hb tf hal vx tv exlimdv2.1 hal vx wv wc
      hb vp wv hb vp tv tt ke kbr hb hb vp tv tt hb vp wv tt tr tf hal vx tv kc
      kct exlimdv2.2 ax-cb2 weqi id oveq2 leq ceq2 hb vp tv tt ke kbr hb hb vp
      tv tt hb vp wv tt tr tf hal vx tv kc kct exlimdv2.2 ax-cb2 weqi id oveq12
      cla4v syl mpd $.
  $}

  ${
    $d y z A $.  $d x y z R $.  $d x y z T $.  $d x y z al $.
    exlimdv.1 $e |- ( R , A ) |= T $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimdv $p |- ( R , ( ? \ x : al . A ) ) |= T $=
      hal vy hal vx ta kl tr tt hal hb vx ta tr ta tt tr ta kct exlimdv.1
      ax-cb1 wctr wl tr hal vx ta kl hal vy tv kc tt hal hb hal vx ta kl hal vy
      tv hal hb vx ta tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr wl hal vy wv wc
      tt tr ta kct exlimdv.1 ax-cb2 hal vx vz ta tt tim kbr hal vx ta kl hal vy
      tv kc tt tim kbr hal vy tv tr hal vy wv hb hb hb hal vx ta kl hal vy tv
      kc tt tim wim hal hb hal vx ta kl hal vy tv hal hb vx ta tr ta tt tr ta
      kct exlimdv.1 ax-cb1 wctr wl hal vy wv wc tt tr ta kct exlimdv.1 ax-cb2
      wov tr ta tt exlimdv.1 ex hal hb hb hb vx hal vx ta kl hal vy tv kc hal
      vz tv tt tim kt wim hal hb hal vx ta kl hal vy tv hal hb vx ta tr ta tt
      tr ta kct exlimdv.1 ax-cb1 wctr wl hal vy wv wc hal vz wv tt tr ta kct
      exlimdv.1 ax-cb2 hal hb hb hb ht ht vx tim hal vz tv wim hal vz wv ax-17
      hal hal hb vx hal vy tv hal vz tv hal vx ta kl kt hal hb vx ta tr ta tt
      tr ta kct exlimdv.1 ax-cb1 wctr wl hal vy wv hal vz wv hal hal hb vx ta
      hal vz tv tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr hal vz wv ax-hbl1 hal
      hal vx hal vy tv hal vz tv hal vy wv hal vz wv ax-17 hbc hal hb vx tt hal
      vz tv tt tr ta kct exlimdv.1 ax-cb2 hal vz wv ax-17 hbov hb hb hb ta tt
      hal vx ta kl hal vy tv kc tim hal vx tv hal vy tv ke kbr wim tr ta tt tr
      ta kct exlimdv.1 ax-cb1 wctr tt tr ta kct exlimdv.1 ax-cb2 hb ta hal vx
      ta kl hal vx tv kc hal vx ta kl hal vy tv kc hal vx tv hal vy tv ke kbr
      tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr ta hal vx ta kl hal vx tv kc ke
      kbr hal vx tv hal vy tv ke kbr hal hal vx tv hal vy tv hal vx wv hal vy
      wv weqi hb hal vx ta kl hal vx tv kc ta kt hal hb hal vx ta kl hal vx tv
      hal hb vx ta tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr wl hal vx wv wc hal
      hb vx ta tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr beta eqcomi a1i hal hb
      hal vx tv hal vy tv hal vx ta kl hal vx tv hal vy tv ke kbr hal hb vx ta
      tr ta tt tr ta kct exlimdv.1 ax-cb1 wctr wl hal vx wv hal vx tv hal vy tv
      ke kbr hal hal vx tv hal vy tv hal vx wv hal vy wv weqi id ceq2 eqtri
      oveq1 insti imp exlimdv2 $.
  $}

  ${
    $d p x A $.  $d p x F $.  $d p x al $.
    ax4e.1 $e |- F : ( al -> bool ) $.
    ax4e.2 $e |- A : al $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    ax4e $p |- ( F A ) |= ( ? F ) $=
      tal hb vp tal hal vx tf hal vx tv kc hb vp tv tim kbr kl kc hb vp tv tim
      kbr kl kc tex tf kc tf ta kc hb vp tal hal vx tf hal vx tv kc hb vp tv
      tim kbr kl kc hb vp tv tim kbr tf ta kc tf ta kc tal hal vx tf hal vx tv
      kc hb vp tv tim kbr kl kc hb vp tv tf ta kc tal hal vx tf hal vx tv kc hb
      vp tv tim kbr kl kc kct tf ta kc hb vp tv hb vp wv tf ta kc tal hal vx tf
      hal vx tv kc hb vp tv tim kbr kl kc hal hb tf ta ax4e.1 ax4e.2 wc hal hb
      ht hb tal hal vx tf hal vx tv kc hb vp tv tim kbr kl hal wal hal hb vx tf
      hal vx tv kc hb vp tv tim kbr hb hb hb tf hal vx tv kc hb vp tv tim wim
      hal hb tf hal vx tv ax4e.1 hal vx wv wc hb vp wv wov wl wc simpl tal hal
      vx tf hal vx tv kc hb vp tv tim kbr kl kc tf ta kc tf ta kc hb vp tv tim
      kbr hal vx tf hal vx tv kc hb vp tv tim kbr ta tf ta kc hb vp tv tim kbr
      hb hb hb tf hal vx tv kc hb vp tv tim wim hal hb tf hal vx tv ax4e.1 hal
      vx wv wc hb vp wv wov ax4e.2 hb hb hb tf hal vx tv kc hb vp tv tf ta kc
      tim hal vx tv ta ke kbr wim hal hb tf hal vx tv ax4e.1 hal vx wv wc hb vp
      wv hal hb hal vx tv ta tf hal vx tv ta ke kbr ax4e.1 hal vx wv hal vx tv
      ta ke kbr hal hal vx tv ta hal vx wv ax4e.2 weqi id ceq2 oveq1 cla4v hal
      hb tf ta ax4e.1 ax4e.2 wc adantl mpd ex alrimiv tex tf kc tal hb vp tal
      hal vx tf hal vx tv kc hb vp tv tim kbr kl kc hb vp tv tim kbr kl kc ke
      kbr tf ta kc hal hb tf ta ax4e.1 ax4e.2 wc hal vx vp tf ax4e.1 exval a1i
      mpbir $.
  $}

  ${
    $d x B $.  $d x C $.  $d x al $.
    cla4ev.1 $e |- A : bool $.
    cla4ev.2 $e |- B : al $.
    cla4ev.3 $e |- [ x : al = B ] |= [ A = C ] $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    cla4ev $p |- C |= ( ? \ x : al . A ) $=
      tc hal vx ta kl tb kc tex hal vx ta kl kc tc hal vx ta kl tb kc tc tc hb
      ta tc hal vx tv tb ke kbr cla4ev.1 cla4ev.3 eqtypi id hal vx ta kl tb kc
      tc ke kbr tc hb ta tc hal vx tv tb ke kbr cla4ev.1 cla4ev.3 eqtypi hal hb
      vx ta tc tb cla4ev.1 cla4ev.2 cla4ev.3 cl a1i mpbir hal tb hal vx ta kl
      hal hb vx ta cla4ev.1 wl cla4ev.2 ax4e syl $.
  $}

  ${
    19.8a.1 $e |- A : bool $.
    $( Existential introduction.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    19.8a $p |- A |= ( ? \ x : al . A ) $=
      ta hal vx ta kl hal vx tv kc tex hal vx ta kl kc ta hal vx ta kl hal vx
      tv kc ta ta 19.8a.1 ax-id hal vx ta kl hal vx tv kc ta ke kbr ta 19.8a.1
      hal hb vx ta 19.8a.1 beta a1i mpbir hal hal vx tv hal vx ta kl hal hb vx
      ta 19.8a.1 wl hal vx wv ax4e syl $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Type definition mechanism
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c typedef $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2d $a wff typedef al ( A , B ) C $.

  ${
    $d x A $.  $d x R $.  $d x F $.
    ax-tdef.1 $e |- B : al $.
    ax-tdef.2 $e |- F : ( al -> bool ) $.
    ax-tdef.3 $e |- T. |= ( F B ) $.
    ax-tdef.4 $e |- typedef be ( A , R ) F $.
    $( Type of the abstraction function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wabs $a |- A : ( al -> be ) $.

    $( Type of the representation function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wrep $a |- R : ( be -> al ) $.

    $( Type of the abstraction function.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wabs $p |- A : ( al -> be ) $=
      hal hbe ta tb tf tr ax-tdef.1 ax-tdef.2 ax-tdef.3 ax-tdef.4 ax-wabs $.

    $( Type of the representation function.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    wrep $p |- R : ( be -> al ) $=
      hal hbe ta tb tf tr ax-tdef.1 ax-tdef.2 ax-tdef.3 ax-tdef.4 ax-wrep $.

    $( The type definition axiom.  The last hypothesis corresponds to the
       actual definition one wants to make; here we are defining a new type
       ` be ` and the definition will provide us with pair of bijections
       ` A , R ` mapping the new type ` be ` to the subset of the old type
       ` al ` such that ` F x ` is true.  In order for this to be a valid
       (conservative) extension, we must ensure that the new type is nonempty,
       and for that purpose we need a witness ` B ` that ` F ` is not always
       false.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-tdef $a |- T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) ,
      ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) ) $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d f x $.
    $( The eta-axiom: a function is determined by its values.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-eta $a |- T. |= ( ! \ f : ( al -> be ) .
      [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] ) $.
  $}

  ${
    $d f x F $.  $d f x al $.  $d f x be $.
    eta.1 $e |- F : ( al -> be ) $.
    $( The eta-axiom: a function is determined by its values.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    eta $p |- T. |= [ \ x : al . ( F x : al ) = F ] $=
      kt tal hal hbe ht vf hal vx hal hbe ht vf tv hal vx tv kc kl hal hbe ht
      vf tv ke kbr kl kc hal vx tf hal vx tv kc kl tf ke kbr hal hbe vx vf
      ax-eta hal hbe ht vf hal vx hal hbe ht vf tv hal vx tv kc kl hal hbe ht
      vf tv ke kbr tf hal vx tf hal vx tv kc kl tf ke kbr hal hbe ht hal hbe ht
      hb hal vx hal hbe ht vf tv hal vx tv kc kl hal hbe ht vf tv ke hal hbe ht
      weq hal hbe vx hal hbe ht vf tv hal vx tv kc hal hbe hal hbe ht vf tv hal
      vx tv hal hbe ht vf wv hal vx wv wc wl hal hbe ht vf wv wov eta.1 hal hbe
      ht hal hbe ht hb hal vx hal hbe ht vf tv hal vx tv kc kl hal hbe ht vf tv
      hal vx tf hal vx tv kc kl ke hal hbe ht vf tv tf ke kbr tf hal hbe ht weq
      hal hbe vx hal hbe ht vf tv hal vx tv kc hal hbe hal hbe ht vf tv hal vx
      tv hal hbe ht vf wv hal vx wv wc wl hal hbe ht vf wv hal hbe vx hal hbe
      ht vf tv hal vx tv kc tf hal vx tv kc hal hbe ht vf tv tf ke kbr hal hbe
      hal hbe ht vf tv hal vx tv hal hbe ht vf wv hal vx wv wc hal hbe hal vx
      tv hal hbe ht vf tv hal hbe ht vf tv tf ke kbr tf hal hbe ht vf wv hal vx
      wv hal hbe ht vf tv tf ke kbr hal hbe ht hal hbe ht vf tv tf hal hbe ht
      vf wv eta.1 weqi id ceq1 leq hal hbe ht vf tv tf ke kbr hal hbe ht hal
      hbe ht vf tv tf hal hbe ht vf wv eta.1 weqi id oveq12 cla4v syl $.
  $}

  ${
    $d p z A $.  $d p z B $.  $d p x y z al $.  $d p be $.
    cbvf.1 $e |- A : be $.
    cbvf.2 $e |- T. |= [ ( \ y : al . A z : al ) = A ] $.
    cbvf.3 $e |- T. |= [ ( \ x : al . B z : al ) = B ] $.
    cbvf.4 $e |- [ x : al = y : al ] |= [ A = B ] $.
    $( Change bound variables in a lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    cbvf $p |- T. |= [ \ x : al . A = \ y : al . B ] $=
      hal hbe ht hal vp hal vx ta kl hal vp tv kc kl hal vp hal vy tb kl hal vp
      tv kc kl kt hal vx ta kl hal vy tb kl hal hbe vp hal vx ta kl hal vp tv
      kc hal hbe hal vx ta kl hal vp tv hal hbe vx ta cbvf.1 wl hal vp wv wc wl
      hal hbe vp hal vx ta kl hal vp tv kc hal vy tb kl hal vp tv kc kt hal hbe
      hal vx ta kl hal vp tv hal hbe vx ta cbvf.1 wl hal vp wv wc hal vy vz hal
      vx ta kl hal vy tv kc tb ke kbr hal vx ta kl hal vp tv kc hal vy tb kl
      hal vp tv kc ke kbr hal vp tv kt hal vp wv hbe hal vx ta kl hal vp tv kc
      hal vy tb kl hal vp tv kc hal hbe hal vx ta kl hal vp tv hal hbe vx ta
      cbvf.1 wl hal vp wv wc hal hbe hal vy tb kl hal vp tv hal hbe vy tb hbe
      ta tb hal vx tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi wl hal vp wv wc
      weqi hal hbe vx vz ta tb hal vy tv cbvf.1 hal vy wv cbvf.4 cbvf.3 hal hal
      vx hal vy tv hal vz tv hal vy wv hal vz wv ax-17 clf hal hbe hbe hb vy
      hal vx ta kl hal vp tv kc hal vz tv hal vy tb kl hal vp tv kc ke kt hbe
      weq hal hbe hal vx ta kl hal vp tv hal hbe vx ta cbvf.1 wl hal vp wv wc
      hal vz wv hal hbe hal vy tb kl hal vp tv hal hbe vy tb hbe ta tb hal vx
      tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi wl hal vp wv wc hal hbe hbe hb
      ht ht vy ke hal vz tv hbe weq hal vz wv ax-17 hal hal hbe vy hal vp tv
      hal vz tv hal vx ta kl kt hal hbe vx ta cbvf.1 wl hal vp wv hal vz wv hal
      hal hbe vy vx ta hal vz tv kt cbvf.1 hal vz wv cbvf.2 hbl hal hal vy hal
      vp tv hal vz tv hal vp wv hal vz wv ax-17 hbc hal hal hbe vy hal vp tv
      hal vz tv hal vy tb kl kt hal hbe vy tb hbe ta tb hal vx tv hal vy tv ke
      kbr cbvf.1 cbvf.4 eqtypi wl hal vp wv hal vz wv hal hal hbe vy tb hal vz
      tv kt hbe ta tb hal vx tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi hal vz wv
      hal vy ta kl hal vz tv kc ta ke kbr kt cbvf.2 ax-cb1 hbl1 hal hal vy hal
      vp tv hal vz tv hal vp wv hal vz wv ax-17 hbc hbov hbe hbe hb hal vx ta
      kl hal vy tv kc tb hal vx ta kl hal vp tv kc ke hal vy tv hal vp tv ke
      kbr hal vy tb kl hal vp tv kc hbe weq hal hbe hal vx ta kl hal vy tv hal
      hbe vx ta cbvf.1 wl hal vy wv wc hbe ta tb hal vx tv hal vy tv ke kbr
      cbvf.1 cbvf.4 eqtypi hal hbe hal vy tv hal vp tv hal vx ta kl hal vy tv
      hal vp tv ke kbr hal hbe vx ta cbvf.1 wl hal vy wv hal vy tv hal vp tv ke
      kbr hal hal vy tv hal vp tv hal vy wv hal vp wv weqi id ceq2 hbe tb hal
      vy tb kl hal vy tv kc hal vy tb kl hal vp tv kc hal vy tv hal vp tv ke
      kbr hbe ta tb hal vx tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi tb hal vy
      tb kl hal vy tv kc ke kbr hal vy tv hal vp tv ke kbr hal vx ta kl hal vy
      tv kc hal vx ta kl hal vp tv kc ke kbr hal vy tv hal vp tv ke kbr hal hbe
      hal vy tv hal vp tv hal vx ta kl hal vy tv hal vp tv ke kbr hal hbe vx ta
      cbvf.1 wl hal vy wv hal vy tv hal vp tv ke kbr hal hal vy tv hal vp tv
      hal vy wv hal vp wv weqi id ceq2 ax-cb1 hbe hal vy tb kl hal vy tv kc tb
      kt hal hbe hal vy tb kl hal vy tv hal hbe vy tb hbe ta tb hal vx tv hal
      vy tv ke kbr cbvf.1 cbvf.4 eqtypi wl hal vy wv wc hal hbe vy tb hbe ta tb
      hal vx tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi beta eqcomi a1i hal hbe
      hal vy tv hal vp tv hal vy tb kl hal vy tv hal vp tv ke kbr hal hbe vy tb
      hbe ta tb hal vx tv hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi wl hal vy wv
      hal vy tv hal vp tv ke kbr hal hal vy tv hal vp tv hal vy wv hal vp wv
      weqi id ceq2 eqtri oveq12 insti leq hal hbe vp hal vx ta kl hal hbe vx ta
      cbvf.1 wl eta hal hbe vp hal vy tb kl hal hbe vy tb hbe ta tb hal vx tv
      hal vy tv ke kbr cbvf.1 cbvf.4 eqtypi wl eta 3eqtr3i $.
  $}

  ${
    $d y z A $.  $d x z B $.  $d x y z al $.  $d y be $.
    cbv.1 $e |- A : be $.
    cbv.2 $e |- [ x : al = y : al ] |= [ A = B ] $.
    $( Change bound variables in a lambda abstraction.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    cbv $p |- T. |= [ \ x : al . A = \ y : al . B ] $=
      hal hbe vx vy vz ta tb cbv.1 hal hbe vy ta hal vz tv cbv.1 hal vz wv
      ax-17 hal hbe vx tb hal vz tv hbe ta tb hal vx tv hal vy tv ke kbr cbv.1
      cbv.2 eqtypi hal vz wv ax-17 cbv.2 cbvf $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z R $.  $d x y z al $.  $d z be $.
    leqf.1 $e |- A : be $.
    leqf.2 $e |- R |= [ A = B ] $.
    leqf.3 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    $( Equality theorem for lambda abstraction, using bound variable instead of
       distinct variables.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    leqf $p |- R |= [ \ x : al . A = \ x : al . B ] $=
      hal hbe ht hal vz hal vx ta kl hal vz tv kc kl hal vz hal vx tb kl hal vz
      tv kc kl tr hal vx ta kl hal vx tb kl hal hbe vz hal vx ta kl hal vz tv
      kc hal hbe hal vx ta kl hal vz tv hal hbe vx ta leqf.1 wl hal vz wv wc wl
      hal hbe vz hal vx ta kl hal vz tv kc hal vx tb kl hal vz tv kc tr hal hbe
      hal vx ta kl hal vz tv hal hbe vx ta leqf.1 wl hal vz wv wc hal vx vy hal
      vx ta kl hal vx tv kc hal vx tb kl hal vx tv kc ke kbr hal vx ta kl hal
      vz tv kc hal vx tb kl hal vz tv kc ke kbr hal vz tv tr tr hbe ta tb tr
      hal vx ta kl hal vx tv kc hal vx tb kl hal vx tv kc leqf.1 leqf.2 hal vx
      ta kl hal vx tv kc ta ke kbr tr ta tb ke kbr tr leqf.2 ax-cb1 hal hbe vx
      ta leqf.1 beta a1i hal vx tb kl hal vx tv kc tb ke kbr tr ta tb ke kbr tr
      leqf.2 ax-cb1 hal hbe vx tb hbe ta tb tr leqf.1 leqf.2 eqtypi beta a1i
      3eqtr4i hal hbe hbe hb vx hal vx ta kl hal vz tv kc hal vy tv hal vx tb
      kl hal vz tv kc ke kt hbe weq hal hbe hal vx ta kl hal vz tv hal hbe vx
      ta leqf.1 wl hal vz wv wc hal vy wv hal hbe hal vx tb kl hal vz tv hal
      hbe vx tb hbe ta tb tr leqf.1 leqf.2 eqtypi wl hal vz wv wc hal hbe hbe
      hb ht ht vx ke hal vy tv hbe weq hal vy wv ax-17 hal hal hbe vx hal vz tv
      hal vy tv hal vx ta kl kt hal hbe vx ta leqf.1 wl hal vz wv hal vy wv hal
      hal hbe vx ta hal vy tv leqf.1 hal vy wv ax-hbl1 hal hal vx hal vz tv hal
      vy tv hal vz wv hal vy wv ax-17 hbc hal hal hbe vx hal vz tv hal vy tv
      hal vx tb kl kt hal hbe vx tb hbe ta tb tr leqf.1 leqf.2 eqtypi wl hal vz
      wv hal vy wv hal hal hbe vx tb hal vy tv hbe ta tb tr leqf.1 leqf.2
      eqtypi hal vy wv ax-hbl1 hal hal vx hal vz tv hal vy tv hal vz wv hal vy
      wv ax-17 hbc hbov leqf.3 hbe hbe hb hal vx ta kl hal vx tv kc hal vx tb
      kl hal vx tv kc hal vx ta kl hal vz tv kc ke hal vx tv hal vz tv ke kbr
      hal vx tb kl hal vz tv kc hbe weq hal hbe hal vx ta kl hal vx tv hal hbe
      vx ta leqf.1 wl hal vx wv wc hal hbe hal vx tb kl hal vx tv hal hbe vx tb
      hbe ta tb tr leqf.1 leqf.2 eqtypi wl hal vx wv wc hal hbe hal vx tv hal
      vz tv hal vx ta kl hal vx tv hal vz tv ke kbr hal hbe vx ta leqf.1 wl hal
      vx wv hal vx tv hal vz tv ke kbr hal hal vx tv hal vz tv hal vx wv hal vz
      wv weqi id ceq2 hal hbe hal vx tv hal vz tv hal vx tb kl hal vx tv hal vz
      tv ke kbr hal hbe vx tb hbe ta tb tr leqf.1 leqf.2 eqtypi wl hal vx wv
      hal vx tv hal vz tv ke kbr hal hal vx tv hal vz tv hal vx wv hal vz wv
      weqi id ceq2 oveq12 hb tr hal vx tv hal vz tv ke kbr hal hal vx tv hal vz
      tv hal vx wv hal vz wv weqi ta tb ke kbr tr leqf.2 ax-cb1 eqid ax-inst
      leq hal vz hal vx ta kl hal vz tv kc kl hal vx ta kl ke kbr tr ta tb ke
      kbr tr leqf.2 ax-cb1 hal hbe vz hal vx ta kl hal hbe vx ta leqf.1 wl eta
      a1i hal vz hal vx tb kl hal vz tv kc kl hal vx tb kl ke kbr tr ta tb ke
      kbr tr leqf.2 ax-cb1 hal hbe vz hal vx tb kl hal hbe vx tb hbe ta tb tr
      leqf.1 leqf.2 eqtypi wl eta a1i 3eqtr3i $.
  $}

  ${
    $d y A $.  $d y R $.  $d x y al $.
    alrimi.1 $e |- R |= A $.
    alrimi.2 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    $( If one can prove ` R |= A ` where ` R ` does not contain ` x ` , then
       ` A ` is true for all ` x ` .  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    alrimi $p |- R |= ( ! \ x : al . A ) $=
      hal vx ta kl hal vx kt kl ke kbr tal hal vx ta kl kc tr hal hb vx vy ta
      kt tr ta tr alrimi.1 ax-cb2 hb kt ta tr wtru ta tr alrimi.1 eqtru eqcomi
      alrimi.2 leqf tal hal vx ta kl kc hal vx ta kl hal vx kt kl ke kbr ke kbr
      tr ta tr alrimi.1 ax-cb1 hal vx hal vx ta kl hal hb vx ta ta tr alrimi.1
      ax-cb2 wl alval a1i mpbir $.
  $}

  ${
    $d y z A $.  $d y z R $.  $d y z T $.  $d x y z al $.
    exlimd.1 $e |- ( R , A ) |= T $.
    exlimd.2 $e |- T. |= [ ( \ x : al . R y : al ) = R ] $.
    exlimd.3 $e |- T. |= [ ( \ x : al . T y : al ) = T ] $.
    $( Existential elimination.  (Contributed by Mario Carneiro,
       9-Oct-2014.) $)
    exlimd $p |- ( R , ( ? \ x : al . A ) ) |= T $=
      tr tex hal vx ta kl kc kct tal hal vz hal vx ta kl hal vz tv kc tt tim
      kbr kl kc tt tt tr ta kct exlimd.1 ax-cb2 tr tex hal vx ta kl kc tal hal
      vz hal vx ta kl hal vz tv kc tt tim kbr kl kc hal vz hal vx ta kl hal vz
      tv kc tt tim kbr tr tr tr hal vx ta kl hal vz tv kc tt tim kbr hb hb hb
      hal vx ta kl hal vz tv kc tt tim wim hal hb hal vx ta kl hal vz tv hal hb
      vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz wv wc tt tr ta
      kct exlimd.1 ax-cb2 wov tr tr ta tt tr ta kct exlimd.1 ax-cb1 wctl id tr
      hal vx ta kl hal vz tv kc tt tim kbr tim kbr tr tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hal vx vy tr ta tt tim kbr tim kbr tr hal vx ta kl
      hal vz tv kc tt tim kbr tim kbr hal vz tv kt hal vz wv hb hb hb tr hal vx
      ta kl hal vz tv kc tt tim kbr tim wim tr ta tt tr ta kct exlimd.1 ax-cb1
      wctl hb hb hb hal vx ta kl hal vz tv kc tt tim wim hal hb hal vx ta kl
      hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz
      wv wc tt tr ta kct exlimd.1 ax-cb2 wov wov kt tr ta tt tim kbr tr kt ta
      tt tim kbr tr ta tt exlimd.1 ex wtru adantl ex hal hb hb hb vx tr hal vy
      tv hal vx ta kl hal vz tv kc tt tim kbr tim kt wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hal vy wv hb hb hb hal vx ta kl hal vz tv kc tt tim
      wim hal hb hal vx ta kl hal vz tv hal hb vx ta tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctr wl hal vz wv wc tt tr ta kct exlimd.1 ax-cb2 wov hal
      hb hb hb ht ht vx tim hal vy tv wim hal vy wv ax-17 exlimd.2 hal hb hb hb
      vx hal vx ta kl hal vz tv kc hal vy tv tt tim kt wim hal hb hal vx ta kl
      hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz
      wv wc hal vy wv tt tr ta kct exlimd.1 ax-cb2 hal hb hb hb ht ht vx tim
      hal vy tv wim hal vy wv ax-17 hal hal hb vx hal vz tv hal vy tv hal vx ta
      kl kt hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz wv
      hal vy wv hal hal hb vx ta hal vy tv tr ta tt tr ta kct exlimd.1 ax-cb1
      wctr hal vy wv ax-hbl1 hal hal vx hal vz tv hal vy tv hal vz wv hal vy wv
      ax-17 hbc exlimd.3 hbov hbov hb hb hb tr ta tt tim kbr tim hal vx tv hal
      vz tv ke kbr hal vx ta kl hal vz tv kc tt tim kbr wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hb hb hb ta tt tim wim tr ta tt tr ta kct exlimd.1
      ax-cb1 wctr tt tr ta kct exlimd.1 ax-cb2 wov hb hb hb ta tt hal vx ta kl
      hal vz tv kc tim hal vx tv hal vz tv ke kbr wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctr tt tr ta kct exlimd.1 ax-cb2 hb ta hal vx ta kl hal
      vx tv kc hal vx ta kl hal vz tv kc hal vx tv hal vz tv ke kbr tr ta tt tr
      ta kct exlimd.1 ax-cb1 wctr ta hal vx ta kl hal vx tv kc ke kbr hal vx tv
      hal vz tv ke kbr hal hal vx tv hal vz tv hal vx wv hal vz wv weqi hb hal
      vx ta kl hal vx tv kc ta kt hal hb hal vx ta kl hal vx tv hal hb vx ta tr
      ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vx wv wc hal hb vx ta tr ta
      tt tr ta kct exlimd.1 ax-cb1 wctr beta eqcomi a1i hal hb hal vx tv hal vz
      tv hal vx ta kl hal vx tv hal vz tv ke kbr hal hb vx ta tr ta tt tr ta
      kct exlimd.1 ax-cb1 wctr wl hal vx wv hal vx tv hal vz tv ke kbr hal hal
      vx tv hal vz tv hal vx wv hal vz wv weqi id ceq2 eqtri oveq1 oveq2 insti
      a1i mpd alrimiv hal hb ht hb tex hal vx ta kl hal wex hal hb vx ta tr ta
      tt tr ta kct exlimd.1 ax-cb1 wctr wl wc adantr tr tex hal vx ta kl kc kct
      tal hb vy tal hal vz hal vx ta kl hal vz tv kc hb vy tv tim kbr kl kc hb
      vy tv tim kbr kl kc tal hal vz hal vx ta kl hal vz tv kc tt tim kbr kl kc
      tt tim kbr tex hal vx ta kl kc tal hb vy tal hal vz hal vx ta kl hal vz
      tv kc hb vy tv tim kbr kl kc hb vy tv tim kbr kl kc tr tex hal vx ta kl
      kc kct tr tex hal vx ta kl kc tr ta tt tr ta kct exlimd.1 ax-cb1 wctl hal
      hb ht hb tex hal vx ta kl hal wex hal hb vx ta tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctr wl wc simpr tex hal vx ta kl kc tal hb vy tal hal vz
      hal vx ta kl hal vz tv kc hb vy tv tim kbr kl kc hb vy tv tim kbr kl kc
      ke kbr tr tex hal vx ta kl kc kct tal hal vz hal vx ta kl hal vz tv kc tt
      tim kbr kl kc tr tex hal vx ta kl kc kct tr tex hal vx ta kl kc tal hal
      vz hal vx ta kl hal vz tv kc tt tim kbr kl kc hal vz hal vx ta kl hal vz
      tv kc tt tim kbr tr tr tr hal vx ta kl hal vz tv kc tt tim kbr hb hb hb
      hal vx ta kl hal vz tv kc tt tim wim hal hb hal vx ta kl hal vz tv hal hb
      vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz wv wc tt tr ta
      kct exlimd.1 ax-cb2 wov tr tr ta tt tr ta kct exlimd.1 ax-cb1 wctl id tr
      hal vx ta kl hal vz tv kc tt tim kbr tim kbr tr tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hal vx vy tr ta tt tim kbr tim kbr tr hal vx ta kl
      hal vz tv kc tt tim kbr tim kbr hal vz tv kt hal vz wv hb hb hb tr hal vx
      ta kl hal vz tv kc tt tim kbr tim wim tr ta tt tr ta kct exlimd.1 ax-cb1
      wctl hb hb hb hal vx ta kl hal vz tv kc tt tim wim hal hb hal vx ta kl
      hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz
      wv wc tt tr ta kct exlimd.1 ax-cb2 wov wov kt tr ta tt tim kbr tr kt ta
      tt tim kbr tr ta tt exlimd.1 ex wtru adantl ex hal hb hb hb vx tr hal vy
      tv hal vx ta kl hal vz tv kc tt tim kbr tim kt wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hal vy wv hb hb hb hal vx ta kl hal vz tv kc tt tim
      wim hal hb hal vx ta kl hal vz tv hal hb vx ta tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctr wl hal vz wv wc tt tr ta kct exlimd.1 ax-cb2 wov hal
      hb hb hb ht ht vx tim hal vy tv wim hal vy wv ax-17 exlimd.2 hal hb hb hb
      vx hal vx ta kl hal vz tv kc hal vy tv tt tim kt wim hal hb hal vx ta kl
      hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz
      wv wc hal vy wv tt tr ta kct exlimd.1 ax-cb2 hal hb hb hb ht ht vx tim
      hal vy tv wim hal vy wv ax-17 hal hal hb vx hal vz tv hal vy tv hal vx ta
      kl kt hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz wv
      hal vy wv hal hal hb vx ta hal vy tv tr ta tt tr ta kct exlimd.1 ax-cb1
      wctr hal vy wv ax-hbl1 hal hal vx hal vz tv hal vy tv hal vz wv hal vy wv
      ax-17 hbc exlimd.3 hbov hbov hb hb hb tr ta tt tim kbr tim hal vx tv hal
      vz tv ke kbr hal vx ta kl hal vz tv kc tt tim kbr wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctl hb hb hb ta tt tim wim tr ta tt tr ta kct exlimd.1
      ax-cb1 wctr tt tr ta kct exlimd.1 ax-cb2 wov hb hb hb ta tt hal vx ta kl
      hal vz tv kc tim hal vx tv hal vz tv ke kbr wim tr ta tt tr ta kct
      exlimd.1 ax-cb1 wctr tt tr ta kct exlimd.1 ax-cb2 hb ta hal vx ta kl hal
      vx tv kc hal vx ta kl hal vz tv kc hal vx tv hal vz tv ke kbr tr ta tt tr
      ta kct exlimd.1 ax-cb1 wctr ta hal vx ta kl hal vx tv kc ke kbr hal vx tv
      hal vz tv ke kbr hal hal vx tv hal vz tv hal vx wv hal vz wv weqi hb hal
      vx ta kl hal vx tv kc ta kt hal hb hal vx ta kl hal vx tv hal hb vx ta tr
      ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vx wv wc hal hb vx ta tr ta
      tt tr ta kct exlimd.1 ax-cb1 wctr beta eqcomi a1i hal hb hal vx tv hal vz
      tv hal vx ta kl hal vx tv hal vz tv ke kbr hal hb vx ta tr ta tt tr ta
      kct exlimd.1 ax-cb1 wctr wl hal vx wv hal vx tv hal vz tv ke kbr hal hal
      vx tv hal vz tv hal vx wv hal vz wv weqi id ceq2 eqtri oveq1 oveq2 insti
      a1i mpd alrimiv hal hb ht hb tex hal vx ta kl hal wex hal hb vx ta tr ta
      tt tr ta kct exlimd.1 ax-cb1 wctr wl wc adantr ax-cb1 hal vz vy hal vx ta
      kl hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl exval a1i mpbi
      hb vy tal hal vz hal vx ta kl hal vz tv kc hb vy tv tim kbr kl kc hb vy
      tv tim kbr tt tal hal vz hal vx ta kl hal vz tv kc tt tim kbr kl kc tt
      tim kbr hb hb hb tal hal vz hal vx ta kl hal vz tv kc hb vy tv tim kbr kl
      kc hb vy tv tim wim hal hb ht hb tal hal vz hal vx ta kl hal vz tv kc hb
      vy tv tim kbr kl hal wal hal hb vz hal vx ta kl hal vz tv kc hb vy tv tim
      kbr hb hb hb hal vx ta kl hal vz tv kc hb vy tv tim wim hal hb hal vx ta
      kl hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal
      vz wv wc hb vy wv wov wl wc hb vy wv wov tt tr ta kct exlimd.1 ax-cb2 hb
      hb hb tal hal vz hal vx ta kl hal vz tv kc hb vy tv tim kbr kl kc hb vy
      tv tal hal vz hal vx ta kl hal vz tv kc tt tim kbr kl kc tim hb vy tv tt
      ke kbr tt wim hal hb ht hb tal hal vz hal vx ta kl hal vz tv kc hb vy tv
      tim kbr kl hal wal hal hb vz hal vx ta kl hal vz tv kc hb vy tv tim kbr
      hb hb hb hal vx ta kl hal vz tv kc hb vy tv tim wim hal hb hal vx ta kl
      hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz
      wv wc hb vy wv wov wl wc hb vy wv hal hb ht hb hal vz hal vx ta kl hal vz
      tv kc hb vy tv tim kbr kl hal vz hal vx ta kl hal vz tv kc tt tim kbr kl
      tal hb vy tv tt ke kbr hal wal hal hb vz hal vx ta kl hal vz tv kc hb vy
      tv tim kbr hb hb hb hal vx ta kl hal vz tv kc hb vy tv tim wim hal hb hal
      vx ta kl hal vz tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr
      wl hal vz wv wc hb vy wv wov wl hal hb vz hal vx ta kl hal vz tv kc hb vy
      tv tim kbr hal vx ta kl hal vz tv kc tt tim kbr hb vy tv tt ke kbr hb hb
      hb hal vx ta kl hal vz tv kc hb vy tv tim wim hal hb hal vx ta kl hal vz
      tv hal hb vx ta tr ta tt tr ta kct exlimd.1 ax-cb1 wctr wl hal vz wv wc
      hb vy wv wov hb hb hb hal vx ta kl hal vz tv kc hb vy tv tim hb vy tv tt
      ke kbr tt wim hal hb hal vx ta kl hal vz tv hal hb vx ta tr ta tt tr ta
      kct exlimd.1 ax-cb1 wctr wl hal vz wv wc hb vy wv hb vy tv tt ke kbr hb
      hb vy tv tt hb vy wv tt tr ta kct exlimd.1 ax-cb2 weqi id oveq2 leq ceq2
      hb vy tv tt ke kbr hb hb vy tv tt hb vy wv tt tr ta kct exlimd.1 ax-cb2
      weqi id oveq12 cla4v syl mpd $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y R $.  $d x y al $.
    alimdv.1 $e |- ( R , A ) |= B $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    alimdv $p |- ( R , ( ! \ x : al . A ) ) |= ( ! \ x : al . B ) $=
      hal vx vy tb tr tal hal vx ta kl kc kct tb tr tal hal vx ta kl kc ta tal
      hal vx ta kl kc tr ta hal vx ta tr ta tb tr ta kct alimdv.1 ax-cb1 wctr
      ax4 tr ta tb tr ta kct alimdv.1 ax-cb1 wctl adantl alimdv.1 syldan hal vx
      tr hal vy tv tal hal vx ta kl kc kt tr ta tb tr ta kct alimdv.1 ax-cb1
      wctl hal vy wv hal hb ht hb tal hal vx ta kl hal wal hal hb vx ta tr ta
      tb tr ta kct alimdv.1 ax-cb1 wctr wl wc hal hb vx tr hal vy tv tr ta tb
      tr ta kct alimdv.1 ax-cb1 wctl hal vy wv ax-17 hal hal hb ht hb vx hal vx
      ta kl hal vy tv tal kt hal wal hal hb vx ta tr ta tb tr ta kct alimdv.1
      ax-cb1 wctr wl hal vy wv hal hal hb ht hb ht vx tal hal vy tv hal wal hal
      vy wv ax-17 hal hal hb vx ta hal vy tv tr ta tb tr ta kct alimdv.1 ax-cb1
      wctr hal vy wv ax-hbl1 hbc hbct alrimi $.

    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    eximdv $p |- ( R , ( ? \ x : al . A ) ) |= ( ? \ x : al . B ) $=
      hal vx vy ta tr tex hal vx tb kl kc tr ta kct tb tex hal vx tb kl kc
      alimdv.1 hal vx tb tb tr ta kct alimdv.1 ax-cb2 19.8a syl hal hb vx tr
      hal vy tv tr ta tb tr ta kct alimdv.1 ax-cb1 wctl hal vy wv ax-17 hal hal
      hb ht hb vx hal vx tb kl hal vy tv tex kt hal wex hal hb vx tb tb tr ta
      kct alimdv.1 ax-cb2 wl hal vy wv hal hal hb ht hb ht vx tex hal vy tv hal
      wex hal vy wv ax-17 hal hal hb vx tb hal vy tv tb tr ta kct alimdv.1
      ax-cb2 hal vy wv ax-hbl1 hbc exlimd $.
  $}

  ${
    $d y A $.  $d x y al $.
    alnex1.1 $e |- A : bool $.
    $( Theorem 19.7 of [Margaris] p. 89.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    alnex $p |- T. |=
        [ ( ! \ x : al . ( ~ A ) ) = ( ~ ( ? \ x : al . A ) ) ] $=
      tal hal vx tne ta kc kl kc tne tex hal vx ta kl kc kc tex hal vx ta kl kc
      tfal tim kbr tne tex hal vx ta kl kc kc tal hal vx tne ta kc kl kc tal
      hal vx tne ta kc kl kc tex hal vx ta kl kc tfal hal vx vy ta tal hal vx
      tne ta kc kl kc tfal tal hal vx tne ta kc kl kc ta tfal alnex1.1 wfal tne
      ta kc ta tfal tim kbr tal hal vx tne ta kc kl kc hal vx tne ta kc hb hb
      tne ta wnot alnex1.1 wc ax4 tne ta kc ta tfal tim kbr ke kbr tal hal vx
      tne ta kc kl kc tne ta kc tal hal vx tne ta kc kl kc hal vx tne ta kc hb
      hb tne ta wnot alnex1.1 wc ax4 ax-cb1 ta alnex1.1 notval a1i mpbi imp hal
      hal hb ht hb vx hal vx tne ta kc kl hal vy tv tal kt hal wal hal hb vx
      tne ta kc hb hb tne ta wnot alnex1.1 wc wl hal vy wv hal hal hb ht hb ht
      vx tal hal vy tv hal wal hal vy wv ax-17 hal hal hb vx tne ta kc hal vy
      tv hb hb tne ta wnot alnex1.1 wc hal vy wv ax-hbl1 hbc hal hb vx tfal hal
      vy tv wfal hal vy wv ax-17 exlimd ex tne tex hal vx ta kl kc kc tex hal
      vx ta kl kc tfal tim kbr ke kbr tal hal vx tne ta kc kl kc tne ta kc tal
      hal vx tne ta kc kl kc hal vx tne ta kc hb hb tne ta wnot alnex1.1 wc ax4
      ax-cb1 tex hal vx ta kl kc hal hb ht hb tex hal vx ta kl hal wex hal hb
      vx ta alnex1.1 wl wc notval a1i mpbir hal vx vy tne ta kc tne tex hal vx
      ta kl kc kc tne tex hal vx ta kl kc kc tne ta kc kt ta tex hal vx ta kl
      kc ta kt tex hal vx ta kl kc hal vx ta alnex1.1 19.8a wtru adantl con3d
      trul hal hb hb vx tex hal vx ta kl kc hal vy tv tne kt wnot hal hb ht hb
      tex hal vx ta kl hal wex hal hb vx ta alnex1.1 wl wc hal vy wv hal hb hb
      ht vx tne hal vy tv wnot hal vy wv ax-17 hal hal hb ht hb vx hal vx ta kl
      hal vy tv tex kt hal wex hal hb vx ta alnex1.1 wl hal vy wv hal hal hb ht
      hb ht vx tex hal vy tv hal wex hal vy wv ax-17 hal hal hb vx ta hal vy tv
      alnex1.1 hal vy wv ax-hbl1 hbc hbc alrimi dedi $.

    $( Forward direction of ~ exnal .  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    exnal1 $p |- ( ? \ x : al . ( ~ A ) ) |= ( ~ ( ! \ x : al . A ) ) $=
      tex hal vx tne ta kc kl kc tne tal hal vx ta kl kc kc kt tal hal vx ta kl
      kc tex hal vx tne ta kc kl kc hal hb ht hb tex hal vx tne ta kc kl hal
      wex hal hb vx tne ta kc hb hb tne ta wnot alnex1.1 wc wl wc kt tal hal vx
      ta kl kc kct tal hal vx tne tne ta kc kc kl kc tne tex hal vx tne ta kc
      kl kc kc hal vx ta tne tne ta kc kc kt ta kt tne tne ta kc kc ta alnex1.1
      notnot1 wtru adantl alimdv tal hal vx tne tne ta kc kc kl kc tne tex hal
      vx tne ta kc kl kc kc tal hal vx tne tne ta kc kc kl kc tal hal vx tne
      tne ta kc kc kl kc hal hb ht hb tal hal vx tne tne ta kc kc kl hal wal
      hal hb vx tne tne ta kc kc hb hb tne tne ta kc wnot hb hb tne ta wnot
      alnex1.1 wc wc wl wc id tal hal vx tne tne ta kc kc kl kc tne tex hal vx
      tne ta kc kl kc kc ke kbr tal hal vx tne tne ta kc kc kl kc hal hb ht hb
      tal hal vx tne tne ta kc kc kl hal wal hal hb vx tne tne ta kc kc hb hb
      tne tne ta kc wnot hb hb tne ta wnot alnex1.1 wc wc wl wc hal vx tne ta
      kc hb hb tne ta wnot alnex1.1 wc alnex a1i mpbi syl con2d trul $.

    isfree.2 $e |- T. |= [ ( \ x : al . A y : al ) = A ] $.
    $( Derive the metamath "is free" predicate in terms of the HOL "is free"
       predicate.  (Contributed by Mario Carneiro, 9-Oct-2014.) $)
    isfree $p |- T. |= [ A ==> ( ! \ x : al . A ) ] $=
      kt ta tal hal vx ta kl kc ta kt tal hal vx ta kl kc hal vx vy ta ta ta
      alnex1.1 id isfree.2 alrimi hal vx ta kl hal vy tv kc ta ke kbr kt
      isfree.2 ax-cb1 adantl ex $.
  $}


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Axioms of infinity and choice
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c 1-1 $.   $( One-to-one function $)
  $c onto $.  $( Onto function $)
  $c @ $.     $( Indefinite descriptor $)

  $( One-to-one function. $)
  tf11 $a term 1-1 $.
  $( Onto function. $)
  tfo $a term onto $.
  $( Indefinite descriptor. $)
  tat $a term @ $.

  $( The type of the indefinite descriptor.  (New usage is discouraged.)
     (Contributed by Mario Carneiro, 10-Oct-2014.) $)
  ax-wat $a |- @ : ( ( al -> bool ) -> al ) $.

  $( The type of the indefinite descriptor.  (Contributed by Mario Carneiro,
     10-Oct-2014.) $)
  wat $p |- @ : ( ( al -> bool ) -> al ) $=
    hal ax-wat $.

  ${
    $d f p x y $.
    $( Define a one-to-one function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-f11 $a |- T. |= [ 1-1 = \ f : ( al -> be ) .
      ( ! \ x : al . ( ! \ y : al .
        [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==>
          [ x : al = y : al ] ] ) ) ] $.

    $( Define an onto function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-fo $a |- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be .
      ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ] $.

    $( Defining property of the indefinite descriptor: it selects an element
       from any type.  This is equivalent to global choice in ZF. (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    ax-ac $a |- T. |= ( ! \ p : ( al -> bool ) .
      ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==>
        ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) ) $.
  $}

  ${
    $d x A $.  $d p x F $.  $d p x al $.
    ac.1 $e |- F : ( al -> bool ) $.
    ac.2 $e |- A : al $.
    $( Defining property of the indefinite descriptor: it selects an element
       from any type.  This is equivalent to global choice in ZF. (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    ac $p |- ( F A ) |= ( F ( @ F ) ) $=
      tf ta kc tf ta kc tf tat tf kc kc hal hb tf tat tf kc ac.1 hal hb ht hal
      tat tf hal wat ac.1 wc wc tf ta kc hal hb tf ta ac.1 ac.2 wc id tf ta kc
      tf tat tf kc kc tim kbr tf ta kc tf ta kc tf ta kc tf ta kc hal hb tf ta
      ac.1 ac.2 wc id ax-cb1 kt tal hal vx tf hal vx tv kc tf tat tf kc kc tim
      kbr kl kc tf ta kc tf tat tf kc kc tim kbr kt tal hal hb ht vp tal hal vx
      hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal hb ht vp tv kc kc
      tim kbr kl kc kl kc tal hal vx tf hal vx tv kc tf tat tf kc kc tim kbr kl
      kc hal vx vp ax-ac hal hb ht vp tal hal vx hal hb ht vp tv hal vx tv kc
      hal hb ht vp tv tat hal hb ht vp tv kc kc tim kbr kl kc tf tal hal vx tf
      hal vx tv kc tf tat tf kc kc tim kbr kl kc hal hb ht hb tal hal vx hal hb
      ht vp tv hal vx tv kc hal hb ht vp tv tat hal hb ht vp tv kc kc tim kbr
      kl hal wal hal hb vx hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal
      hb ht vp tv kc kc tim kbr hb hb hb hal hb ht vp tv hal vx tv kc hal hb ht
      vp tv tat hal hb ht vp tv kc kc tim wim hal hb hal hb ht vp tv hal vx tv
      hal hb ht vp wv hal vx wv wc hal hb hal hb ht vp tv tat hal hb ht vp tv
      kc hal hb ht vp wv hal hb ht hal tat hal hb ht vp tv hal wat hal hb ht vp
      wv wc wc wov wl wc ac.1 hal hb ht hb hal vx hal hb ht vp tv hal vx tv kc
      hal hb ht vp tv tat hal hb ht vp tv kc kc tim kbr kl hal vx tf hal vx tv
      kc tf tat tf kc kc tim kbr kl tal hal hb ht vp tv tf ke kbr hal wal hal
      hb vx hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal hb ht vp tv kc
      kc tim kbr hb hb hb hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal
      hb ht vp tv kc kc tim wim hal hb hal hb ht vp tv hal vx tv hal hb ht vp
      wv hal vx wv wc hal hb hal hb ht vp tv tat hal hb ht vp tv kc hal hb ht
      vp wv hal hb ht hal tat hal hb ht vp tv hal wat hal hb ht vp wv wc wc wov
      wl hal hb vx hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal hb ht
      vp tv kc kc tim kbr tf hal vx tv kc tf tat tf kc kc tim kbr hal hb ht vp
      tv tf ke kbr hb hb hb hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat
      hal hb ht vp tv kc kc tim wim hal hb hal hb ht vp tv hal vx tv hal hb ht
      vp wv hal vx wv wc hal hb hal hb ht vp tv tat hal hb ht vp tv kc hal hb
      ht vp wv hal hb ht hal tat hal hb ht vp tv hal wat hal hb ht vp wv wc wc
      wov hb hb hb hal hb ht vp tv hal vx tv kc hal hb ht vp tv tat hal hb ht
      vp tv kc kc tf hal vx tv kc tim hal hb ht vp tv tf ke kbr tf tat tf kc kc
      wim hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv hal vx wv wc hal hb
      hal hb ht vp tv tat hal hb ht vp tv kc hal hb ht vp wv hal hb ht hal tat
      hal hb ht vp tv hal wat hal hb ht vp wv wc wc hal hb hal vx tv hal hb ht
      vp tv hal hb ht vp tv tf ke kbr tf hal hb ht vp wv hal vx wv hal hb ht vp
      tv tf ke kbr hal hb ht hal hb ht vp tv tf hal hb ht vp wv ac.1 weqi id
      ceq1 hal hb tat hal hb ht vp tv kc tat tf kc hal hb ht vp tv hal hb ht vp
      tv tf ke kbr tf hal hb ht vp wv hal hb ht hal tat hal hb ht vp tv hal wat
      hal hb ht vp wv wc hal hb ht vp tv tf ke kbr hal hb ht hal hb ht vp tv tf
      hal hb ht vp wv ac.1 weqi id hal hb ht hal hal hb ht vp tv tf tat hal hb
      ht vp tv tf ke kbr hal wat hal hb ht vp wv hal hb ht vp tv tf ke kbr hal
      hb ht hal hb ht vp tv tf hal hb ht vp wv ac.1 weqi id ceq2 ceq12 oveq12
      leq ceq2 cla4v syl hal vx tf hal vx tv kc tf tat tf kc kc tim kbr ta tf
      ta kc tf tat tf kc kc tim kbr hb hal hb ht vp tv hal vx tv kc hal hb ht
      vp tv tat hal hb ht vp tv kc kc tim kbr tf hal vx tv kc tf tat tf kc kc
      tim kbr hal hb ht vp tv tf ke kbr hb hb hb hal hb ht vp tv hal vx tv kc
      hal hb ht vp tv tat hal hb ht vp tv kc kc tim wim hal hb hal hb ht vp tv
      hal vx tv hal hb ht vp wv hal vx wv wc hal hb hal hb ht vp tv tat hal hb
      ht vp tv kc hal hb ht vp wv hal hb ht hal tat hal hb ht vp tv hal wat hal
      hb ht vp wv wc wc wov hb hb hb hal hb ht vp tv hal vx tv kc hal hb ht vp
      tv tat hal hb ht vp tv kc kc tf hal vx tv kc tim hal hb ht vp tv tf ke
      kbr tf tat tf kc kc wim hal hb hal hb ht vp tv hal vx tv hal hb ht vp wv
      hal vx wv wc hal hb hal hb ht vp tv tat hal hb ht vp tv kc hal hb ht vp
      wv hal hb ht hal tat hal hb ht vp tv hal wat hal hb ht vp wv wc wc hal hb
      hal vx tv hal hb ht vp tv hal hb ht vp tv tf ke kbr tf hal hb ht vp wv
      hal vx wv hal hb ht vp tv tf ke kbr hal hb ht hal hb ht vp tv tf hal hb
      ht vp wv ac.1 weqi id ceq1 hal hb tat hal hb ht vp tv kc tat tf kc hal hb
      ht vp tv hal hb ht vp tv tf ke kbr tf hal hb ht vp wv hal hb ht hal tat
      hal hb ht vp tv hal wat hal hb ht vp wv wc hal hb ht vp tv tf ke kbr hal
      hb ht hal hb ht vp tv tf hal hb ht vp wv ac.1 weqi id hal hb ht hal hal
      hb ht vp tv tf tat hal hb ht vp tv tf ke kbr hal wat hal hb ht vp wv hal
      hb ht vp tv tf ke kbr hal hb ht hal hb ht vp tv tf hal hb ht vp wv ac.1
      weqi id ceq2 ceq12 oveq12 eqtypi ac.2 hb hb hb tf hal vx tv kc tf tat tf
      kc kc tf ta kc tim hal vx tv ta ke kbr wim hal hb tf hal vx tv ac.1 hal
      vx wv wc hal hb tf tat tf kc ac.1 hal hb ht hal tat tf hal wat ac.1 wc wc
      hal hb hal vx tv ta tf hal vx tv ta ke kbr ac.1 hal vx wv hal vx tv ta ke
      kbr hal hal vx tv ta hal vx wv ac.2 weqi id ceq2 oveq1 cla4v syl a1i mpd
      $.
  $}

  ${
    $d x F $.  $d x al $.
    dfex2.1 $e |- F : ( al -> bool ) $.
    $( Alternative definition of the "there exists" quantifier.  (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    dfex2 $p |- T. |= [ ( ? F ) = ( F ( @ F ) ) ] $=
      kt tex tf kc tf tat tf kc kc hal vx tf kt tf tat tf kc kc dfex2.1 tf hal
      vx tv kc kt tf tat tf kc kc hal hal vx tv tf dfex2.1 hal vx wv ac wtru
      adantl exlimdv2 tf tat tf kc kc kt tex tf kc hal tat tf kc tf dfex2.1 hal
      hb ht hal tat tf hal wat dfex2.1 wc ax4e wtru adantl ded $.
  $}

  ${
    $d x y A $.  $d x al $.
    exmid.1 $e |- A : bool $.
    $( Diaconescu's theorem, which derives the law of the excluded middle from
       the axiom of choice.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    exmid $p |- T. |= [ A \/ ( ~ A ) ] $=
      tat hb vx hb vx tv ta tor kbr kl kc ta kt ta tne ta kc tor kbr hb hb ht
      hb tat hb vx hb vx tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr
      hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov wl wc exmid.1 hb hb hb
      ta tne ta kc tor wor exmid.1 hb hb tne ta wnot exmid.1 wc wov hb vx hb vx
      tv ta tor kbr kl tat hb vx hb vx tv ta tor kbr kl kc kc tat hb vx hb vx
      tv ta tor kbr kl kc ta tor kbr kt kt hb vx hb vx tv ta tor kbr kl kt kc
      hb vx hb vx tv ta tor kbr kl tat hb vx hb vx tv ta tor kbr kl kc kc kt ta
      tor kbr hb vx hb vx tv ta tor kbr kl kt kc kt kt ta wtru exmid.1 orc hb
      hb vx hb vx tv ta tor kbr kt ta tor kbr kt hb hb hb hb vx tv ta tor wor
      hb vx wv exmid.1 wov wtru hb hb hb hb vx tv ta kt tor hb vx tv kt ke kbr
      wor hb vx wv exmid.1 hb vx tv kt ke kbr hb hb vx tv kt hb vx wv wtru weqi
      id oveq1 cl mpbir hb kt hb vx hb vx tv ta tor kbr kl hb hb vx hb vx tv ta
      tor kbr hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov wl wtru ac syl
      hb hb vx vy hb vx tv ta tor kbr tat hb vx hb vx tv ta tor kbr kl kc ta
      tor kbr tat hb vx hb vx tv ta tor kbr kl kc hb hb hb hb vx tv ta tor wor
      hb vx wv exmid.1 wov hb hb ht hb tat hb vx hb vx tv ta tor kbr kl hb wat
      hb hb vx hb vx tv ta tor kbr hb hb hb hb vx tv ta tor wor hb vx wv
      exmid.1 wov wl wc hb hb hb hb vx tv ta tat hb vx hb vx tv ta tor kbr kl
      kc tor hb vx tv tat hb vx hb vx tv ta tor kbr kl kc ke kbr wor hb vx wv
      exmid.1 hb vx tv tat hb vx hb vx tv ta tor kbr kl kc ke kbr hb hb vx tv
      tat hb vx hb vx tv ta tor kbr kl kc hb vx wv hb hb ht hb tat hb vx hb vx
      tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx tv ta
      tor wor hb vx wv exmid.1 wov wl wc weqi id oveq1 hb hb hb hb vx tat hb vx
      hb vx tv ta tor kbr kl kc hb vy tv ta tor kt wor hb hb ht hb tat hb vx hb
      vx tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx tv
      ta tor wor hb vx wv exmid.1 wov wl wc hb vy wv exmid.1 hb hb hb hb ht ht
      vx tor hb vy tv wor hb vy wv ax-17 hb hb hb ht hb vx hb vx hb vx tv ta
      tor kbr kl hb vy tv tat kt hb wat hb hb vx hb vx tv ta tor kbr hb hb hb
      hb vx tv ta tor wor hb vx wv exmid.1 wov wl hb vy wv hb hb hb ht hb ht vx
      tat hb vy tv hb wat hb vy wv ax-17 hb hb hb vx hb vx tv ta tor kbr hb vy
      tv hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov hb vy wv ax-hbl1 hbc
      hb hb vx ta hb vy tv exmid.1 hb vy wv ax-17 hbov hb hb hb ht hb vx hb vx
      hb vx tv ta tor kbr kl hb vy tv tat kt hb wat hb hb vx hb vx tv ta tor
      kbr hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov wl hb vy wv hb hb
      hb ht hb ht vx tat hb vy tv hb wat hb vy wv ax-17 hb hb hb vx hb vx tv ta
      tor kbr hb vy tv hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov hb vy
      wv ax-hbl1 hbc clf mpbi tat hb vx hb vx tv ta tor kbr kl kc kt ta tne ta
      kc tor kbr tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc ta tat hb vx
      hb vx tv ta tor kbr kl kc ta tne ta kc tor kbr hb hb tne tat hb vx tne hb
      vx tv kc ta tor kbr kl kc wnot hb hb ht hb tat hb vx tne hb vx tv kc ta
      tor kbr kl hb wat hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx
      tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc wc
      exmid.1 hb hb hb ta tne ta kc tor wor exmid.1 hb hb tne ta wnot exmid.1
      wc wov tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc ta tor kbr tat
      hb vx hb vx tv ta tor kbr kl kc hb hb ht hb tat hb vx hb vx tv ta tor kbr
      kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx tv ta tor wor hb vx
      wv exmid.1 wov wl wc hb vx tne hb vx tv kc ta tor kbr kl tat hb vx tne hb
      vx tv kc ta tor kbr kl kc kc tne tat hb vx tne hb vx tv kc ta tor kbr kl
      kc kc ta tor kbr kt kt hb vx tne hb vx tv kc ta tor kbr kl tfal kc hb vx
      tne hb vx tv kc ta tor kbr kl tat hb vx tne hb vx tv kc ta tor kbr kl kc
      kc kt ta tor kbr hb vx tne hb vx tv kc ta tor kbr kl tfal kc kt kt ta
      wtru exmid.1 orc hb hb vx tne hb vx tv kc ta tor kbr kt ta tor kbr tfal
      hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc
      exmid.1 wov wfal hb hb hb tne hb vx tv kc ta kt tor hb vx tv tfal ke kbr
      wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 hb tne hb vx tv kc tne
      tfal kc kt hb vx tv tfal ke kbr hb hb tne hb vx tv wnot hb vx wv wc hb hb
      hb vx tv tfal tne hb vx tv tfal ke kbr wnot hb vx wv hb vx tv tfal ke kbr
      hb hb vx tv tfal hb vx wv wfal weqi id ceq2 tne tfal kc kt ke kbr hb vx
      tv tfal ke kbr hb hb vx tv tfal hb vx wv wfal weqi hb kt tne tfal kc kt
      wtru tne tfal kc kt tfal tfal tim kbr tne tfal kc kt kt tfal tfal kt tfal
      wtru wfal simpr ex tfal wfal notval mpbir eqtru eqcomi a1i eqtri oveq1 cl
      mpbir hb tfal hb vx tne hb vx tv kc ta tor kbr kl hb hb vx tne hb vx tv
      kc ta tor kbr hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot
      hb vx wv wc exmid.1 wov wl wfal ac syl hb hb vx vy tne hb vx tv kc ta tor
      kbr tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc ta tor kbr tat hb
      vx tne hb vx tv kc ta tor kbr kl kc hb hb hb tne hb vx tv kc ta tor wor
      hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov hb hb ht hb tat hb vx tne
      hb vx tv kc ta tor kbr kl hb wat hb hb vx tne hb vx tv kc ta tor kbr hb
      hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc
      exmid.1 wov wl wc hb hb hb tne hb vx tv kc ta tne tat hb vx tne hb vx tv
      kc ta tor kbr kl kc kc tor hb vx tv tat hb vx tne hb vx tv kc ta tor kbr
      kl kc ke kbr wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 hb hb hb vx
      tv tat hb vx tne hb vx tv kc ta tor kbr kl kc tne hb vx tv tat hb vx tne
      hb vx tv kc ta tor kbr kl kc ke kbr wnot hb vx wv hb vx tv tat hb vx tne
      hb vx tv kc ta tor kbr kl kc ke kbr hb hb vx tv tat hb vx tne hb vx tv kc
      ta tor kbr kl kc hb vx wv hb hb ht hb tat hb vx tne hb vx tv kc ta tor
      kbr kl hb wat hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx tv
      kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc weqi
      id ceq2 oveq1 hb hb hb hb vx tne tat hb vx tne hb vx tv kc ta tor kbr kl
      kc kc hb vy tv ta tor kt wor hb hb tne tat hb vx tne hb vx tv kc ta tor
      kbr kl kc wnot hb hb ht hb tat hb vx tne hb vx tv kc ta tor kbr kl hb wat
      hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx tv kc ta tor wor
      hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc wc hb vy wv exmid.1
      hb hb hb hb ht ht vx tor hb vy tv wor hb vy wv ax-17 hb hb hb vx tat hb
      vx tne hb vx tv kc ta tor kbr kl kc hb vy tv tne kt wnot hb hb ht hb tat
      hb vx tne hb vx tv kc ta tor kbr kl hb wat hb hb vx tne hb vx tv kc ta
      tor kbr hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx
      wv wc exmid.1 wov wl wc hb vy wv hb hb hb ht vx tne hb vy tv wnot hb vy
      wv ax-17 hb hb hb ht hb vx hb vx tne hb vx tv kc ta tor kbr kl hb vy tv
      tat kt hb wat hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx tv
      kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl hb vy wv
      hb hb hb ht hb ht vx tat hb vy tv hb wat hb vy wv ax-17 hb hb hb vx tne
      hb vx tv kc ta tor kbr hb vy tv hb hb hb tne hb vx tv kc ta tor wor hb hb
      tne hb vx tv wnot hb vx wv wc exmid.1 wov hb vy wv ax-hbl1 hbc hbc hb hb
      vx ta hb vy tv exmid.1 hb vy wv ax-17 hbov hb hb hb ht hb vx hb vx tne hb
      vx tv kc ta tor kbr kl hb vy tv tat kt hb wat hb hb vx tne hb vx tv kc ta
      tor kbr hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx
      wv wc exmid.1 wov wl hb vy wv hb hb hb ht hb ht vx tat hb vy tv hb wat hb
      vy wv ax-17 hb hb hb vx tne hb vx tv kc ta tor kbr hb vy tv hb hb hb tne
      hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov hb
      vy wv ax-hbl1 hbc clf mpbi a1i tat hb vx hb vx tv ta tor kbr kl kc tne
      tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct tne ta kc ta tne ta kc
      tor kbr ta tfal tim kbr tne ta kc tat hb vx hb vx tv ta tor kbr kl kc tne
      tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct tat hb vx hb vx tv ta
      tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct ta
      tfal tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta
      tor kbr kl kc kc kct ta kct tat hb vx tne hb vx tv kc ta tor kbr kl kc
      tfal wfal tat hb vx hb vx tv ta tor kbr kl kc tat hb vx tne hb vx tv kc
      ta tor kbr kl kc tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb
      vx tv kc ta tor kbr kl kc kc kct ta kct tat hb vx hb vx tv ta tor kbr kl
      kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct ta kct tat hb vx
      hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc
      kc tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta
      tor kbr kl kc kc kct ta tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx
      tne hb vx tv kc ta tor kbr kl kc kc hb hb ht hb tat hb vx hb vx tv ta tor
      kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx tv ta tor wor
      hb vx wv exmid.1 wov wl wc hb hb tne tat hb vx tne hb vx tv kc ta tor kbr
      kl kc wnot hb hb ht hb tat hb vx tne hb vx tv kc ta tor kbr kl hb wat hb
      hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx tv kc ta tor wor hb
      hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc wc wct exmid.1 simpl
      simpld ta tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv
      kc ta tor kbr kl kc kc kct tat hb vx hb vx tv ta tor kbr kl kc tat hb vx
      tne hb vx tv kc ta tor kbr kl kc ke kbr hb hb ht hb hb vx hb vx tv ta tor
      kbr kl hb vx tne hb vx tv kc ta tor kbr kl tat ta hb wat hb hb vx hb vx
      tv ta tor kbr hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov wl hb hb
      vx hb vx tv ta tor kbr tne hb vx tv kc ta tor kbr ta hb hb hb hb vx tv ta
      tor wor hb vx wv exmid.1 wov hb hb vx tv ta tor kbr kt tne hb vx tv kc ta
      tor kbr ta hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov hb kt hb vx
      tv ta tor kbr ta wtru hb vx tv ta tor kbr ta hb vx tv ta hb vx wv exmid.1
      olc eqtru eqcomi tne hb vx tv kc ta tor kbr ta tne hb vx tv kc ta hb hb
      tne hb vx tv wnot hb vx wv wc exmid.1 olc eqtru eqtri leq ceq2 tat hb vx
      hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc
      kc hb hb ht hb tat hb vx hb vx tv ta tor kbr kl hb wat hb hb vx hb vx tv
      ta tor kbr hb hb hb hb vx tv ta tor wor hb vx wv exmid.1 wov wl wc hb hb
      tne tat hb vx tne hb vx tv kc ta tor kbr kl kc wnot hb hb ht hb tat hb vx
      tne hb vx tv kc ta tor kbr kl hb wat hb hb vx tne hb vx tv kc ta tor kbr
      hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc
      exmid.1 wov wl wc wc wct adantl mpbi tne tat hb vx tne hb vx tv kc ta tor
      kbr kl kc kc tat hb vx tne hb vx tv kc ta tor kbr kl kc tfal tim kbr tat
      hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr
      kl kc kc kct ta kct tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne
      hb vx tv kc ta tor kbr kl kc kc kct ta kct tat hb vx hb vx tv ta tor kbr
      kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc tat hb vx hb vx
      tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct
      ta tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta
      tor kbr kl kc kc hb hb ht hb tat hb vx hb vx tv ta tor kbr kl hb wat hb
      hb vx hb vx tv ta tor kbr hb hb hb hb vx tv ta tor wor hb vx wv exmid.1
      wov wl wc hb hb tne tat hb vx tne hb vx tv kc ta tor kbr kl kc wnot hb hb
      ht hb tat hb vx tne hb vx tv kc ta tor kbr kl hb wat hb hb vx tne hb vx
      tv kc ta tor kbr hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv
      wnot hb vx wv wc exmid.1 wov wl wc wc wct exmid.1 simpl simprd tne tat hb
      vx tne hb vx tv kc ta tor kbr kl kc kc tat hb vx tne hb vx tv kc ta tor
      kbr kl kc tfal tim kbr ke kbr tat hb vx hb vx tv ta tor kbr kl kc tne tat
      hb vx tne hb vx tv kc ta tor kbr kl kc kc kct ta kct tat hb vx hb vx tv
      ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc kct
      tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne hb vx tv kc ta tor
      kbr kl kc kc kct ta kct tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx
      tne hb vx tv kc ta tor kbr kl kc kc kct ta tat hb vx hb vx tv ta tor kbr
      kl kc tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc hb hb ht hb tat
      hb vx hb vx tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb
      hb vx tv ta tor wor hb vx wv exmid.1 wov wl wc hb hb tne tat hb vx tne hb
      vx tv kc ta tor kbr kl kc wnot hb hb ht hb tat hb vx tne hb vx tv kc ta
      tor kbr kl hb wat hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx
      tv kc ta tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc wc
      wct exmid.1 simpl ax-cb1 tat hb vx tne hb vx tv kc ta tor kbr kl kc hb hb
      ht hb tat hb vx tne hb vx tv kc ta tor kbr kl hb wat hb hb vx tne hb vx
      tv kc ta tor kbr hb hb hb tne hb vx tv kc ta tor wor hb hb tne hb vx tv
      wnot hb vx wv wc exmid.1 wov wl wc notval a1i mpbi mpd ex tne ta kc ta
      tfal tim kbr ke kbr tat hb vx hb vx tv ta tor kbr kl kc tne tat hb vx tne
      hb vx tv kc ta tor kbr kl kc kc kct tat hb vx hb vx tv ta tor kbr kl kc
      tne tat hb vx tne hb vx tv kc ta tor kbr kl kc kc hb hb ht hb tat hb vx
      hb vx tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx
      tv ta tor wor hb vx wv exmid.1 wov wl wc hb hb tne tat hb vx tne hb vx tv
      kc ta tor kbr kl kc wnot hb hb ht hb tat hb vx tne hb vx tv kc ta tor kbr
      kl hb wat hb hb vx tne hb vx tv kc ta tor kbr hb hb hb tne hb vx tv kc ta
      tor wor hb hb tne hb vx tv wnot hb vx wv wc exmid.1 wov wl wc wc wct ta
      exmid.1 notval a1i mpbir ta tne ta kc exmid.1 hb hb tne ta wnot exmid.1
      wc olc syl ta tat hb vx hb vx tv ta tor kbr kl kc ta tne ta kc tor kbr ta
      tne ta kc exmid.1 hb hb tne ta wnot exmid.1 wc orc hb hb ht hb tat hb vx
      hb vx tv ta tor kbr kl hb wat hb hb vx hb vx tv ta tor kbr hb hb hb hb vx
      tv ta tor wor hb vx wv exmid.1 wov wl wc adantl ecase wtru adantl ta kt
      ta tne ta kc tor kbr ta tne ta kc exmid.1 hb hb tne ta wnot exmid.1 wc
      orc wtru adantl ecase $.

    $( Rule of double negation.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    notnot $p |- T. |= [ A = ( ~ ( ~ A ) ) ] $=
      ta tne tne ta kc kc ta exmid.1 notnot1 ta tne ta kc tne tne ta kc kc ta
      exmid.1 hb hb tne ta wnot exmid.1 wc exmid.1 ta tne ta kc tor kbr tne tne
      ta kc kc tne tne ta kc kc ta ta exmid.1 notnot1 ax-cb2 ta exmid.1 exmid
      a1i tne tne ta kc kc ta tne tne ta kc kc ta ta exmid.1 notnot1 ax-cb2
      exmid.1 simpr tne tne ta kc kc tne ta kc kct tfal ta tne tne ta kc kc tne
      ta kc tfal hb hb tne ta wnot exmid.1 wc wfal tne tne ta kc kc tne ta kc
      tfal tim kbr tne tne ta kc kc tne tne ta kc kc tne tne ta kc kc ta ta
      exmid.1 notnot1 ax-cb2 id tne tne ta kc kc tne ta kc tfal tim kbr ke kbr
      tne tne ta kc kc tne tne ta kc kc ta ta exmid.1 notnot1 ax-cb2 tne ta kc
      hb hb tne ta wnot exmid.1 wc notval a1i mpbi imp ta exmid.1 pm2.21 syl
      ecase dedi $.

    $( Theorem 19.14 of [Margaris] p. 90.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    exnal $p |- T. |=
      [ ( ? \ x : al . ( ~ A ) ) = ( ~ ( ! \ x : al . A ) ) ] $=
      hb tne tne tex hal vx tne ta kc kl kc kc kc tne tal hal vx tne tne ta kc
      kc kl kc kc kt tex hal vx tne ta kc kl kc tne tal hal vx ta kl kc kc hb
      hb tne tne tex hal vx tne ta kc kl kc kc wnot hb hb tne tex hal vx tne ta
      kc kl kc wnot hal hb ht hb tex hal vx tne ta kc kl hal wex hal hb vx tne
      ta kc hb hb tne ta wnot exmid.1 wc wl wc wc wc hb hb tne tex hal vx tne
      ta kc kl kc kc tal hal vx tne tne ta kc kc kl kc tne kt wnot hb hb tne
      tex hal vx tne ta kc kl kc wnot hal hb ht hb tex hal vx tne ta kc kl hal
      wex hal hb vx tne ta kc hb hb tne ta wnot exmid.1 wc wl wc wc hb tal hal
      vx tne tne ta kc kc kl kc tne tex hal vx tne ta kc kl kc kc kt hal hb ht
      hb tal hal vx tne tne ta kc kc kl hal wal hal hb vx tne tne ta kc kc hb
      hb tne tne ta kc wnot hb hb tne ta wnot exmid.1 wc wc wl wc hal vx tne ta
      kc hb hb tne ta wnot exmid.1 wc alnex eqcomi ceq2 tex hal vx tne ta kc kl
      kc hal hb ht hb tex hal vx tne ta kc kl hal wex hal hb vx tne ta kc hb hb
      tne ta wnot exmid.1 wc wl wc notnot hb hb tal hal vx ta kl kc tal hal vx
      tne tne ta kc kc kl kc tne kt wnot hal hb ht hb tal hal vx ta kl hal wal
      hal hb vx ta exmid.1 wl wc hal hb ht hb hal vx ta kl hal vx tne tne ta kc
      kc kl tal kt hal wal hal hb vx ta exmid.1 wl hal hb vx ta tne tne ta kc
      kc kt exmid.1 ta exmid.1 notnot leq ceq2 ceq2 3eqtr4i $.
  $}

  $( The axiom of infinity: the set of "individuals" is not Dedekind-finite.
     Using the axiom of choice, we can show that this is equivalent to an
     embedding of the natural numbers in ` ind ` .  (Contributed by Mario
     Carneiro, 10-Oct-2014.) $)
  ax-inf $a |- T. |= ( ? \ f : ( ind -> ind ) .
    [ ( 1-1 f : ( ind -> ind ) ) /\ ( ~ ( onto f : ( ind -> ind ) ) ) ] ) $.


$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Rederive the Metamath axioms
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    ax1.1 $e |- R : bool $.
    ax1.2 $e |- S : bool $.
    $( Axiom _Simp_.  Axiom A1 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    ax1 $p |- T. |= [ R ==> [ S ==> R ] ] $=
      kt tr ts tr tim kbr kt tr kct ts tr kt tr kct ts tr kt tr wtru ax1.1
      simpr ax1.2 adantr ex ex $.

    ax2.3 $e |- T : bool $.
    $( Axiom _Frege_.  Axiom A2 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 9-Oct-2014.) $)
    ax2 $p |- T. |=
      [ [ R ==> [ S ==> T ] ] ==> [ [ R ==> S ] ==> [ R ==> T ] ] ] $=
      kt tr ts tt tim kbr tim kbr tr ts tim kbr tr tt tim kbr tim kbr tr ts tt
      tim kbr tim kbr kt tr ts tim kbr tr tt tim kbr tim kbr tr ts tt tim kbr
      tim kbr tr ts tim kbr tr tt tim kbr tr ts tt tim kbr tim kbr tr ts tim
      kbr kct tr tt tr ts tt tim kbr tim kbr tr ts tim kbr kct tr kct ts tt
      ax2.3 tr ts tt tim kbr tim kbr tr ts tim kbr kct tr kct tr ts ax1.2 tr ts
      tt tim kbr tim kbr tr ts tim kbr kct tr tr ts tt tim kbr tim kbr tr ts
      tim kbr hb hb hb tr ts tt tim kbr tim wim ax1.1 hb hb hb ts tt tim wim
      ax1.2 ax2.3 wov wov hb hb hb tr ts tim wim ax1.1 ax1.2 wov wct ax1.1
      simpr tr ts tt tim kbr tim kbr tr ts tim kbr kct tr kct tr ts tt tim kbr
      tim kbr tr ts tim kbr tr ts tt tim kbr tim kbr tr ts tim kbr kct tr tr ts
      tt tim kbr tim kbr tr ts tim kbr hb hb hb tr ts tt tim kbr tim wim ax1.1
      hb hb hb ts tt tim wim ax1.2 ax2.3 wov wov hb hb hb tr ts tim wim ax1.1
      ax1.2 wov wct ax1.1 simpl simprd mpd tr ts tt tim kbr tim kbr tr ts tim
      kbr kct tr kct tr ts tt tim kbr hb hb hb ts tt tim wim ax1.2 ax2.3 wov tr
      ts tt tim kbr tim kbr tr ts tim kbr kct tr tr ts tt tim kbr tim kbr tr ts
      tim kbr hb hb hb tr ts tt tim kbr tim wim ax1.1 hb hb hb ts tt tim wim
      ax1.2 ax2.3 wov wov hb hb hb tr ts tim wim ax1.1 ax1.2 wov wct ax1.1
      simpr tr ts tt tim kbr tim kbr tr ts tim kbr kct tr kct tr ts tt tim kbr
      tim kbr tr ts tim kbr tr ts tt tim kbr tim kbr tr ts tim kbr kct tr tr ts
      tt tim kbr tim kbr tr ts tim kbr hb hb hb tr ts tt tim kbr tim wim ax1.1
      hb hb hb ts tt tim wim ax1.2 ax2.3 wov wov hb hb hb tr ts tim wim ax1.1
      ax1.2 wov wct ax1.1 simpl simpld mpd mpd ex ex wtru adantl ex $.
  $}

  ${
    ax3.1 $e |- R : bool $.
    ax3.2 $e |- S : bool $.
    $( Axiom _Transp_.  Axiom A3 of [Margaris] p. 49.  (Contributed by Mario
       Carneiro, 10-Oct-2014.) $)
    ax3 $p |- T. |= [ [ ( ~ R ) ==> ( ~ S ) ] ==> [ S ==> R ] ] $=
      kt tne tr kc tne ts kc tim kbr ts tr tim kbr tne tr kc tne ts kc tim kbr
      kt ts tr tim kbr tne tr kc tne ts kc tim kbr ts tr tr tne tr kc tne tr kc
      tne ts kc tim kbr ts kct tr ax3.1 hb hb tne tr wnot ax3.1 wc ax3.1 tr tne
      tr kc tor kbr tne tr kc tne ts kc tim kbr ts kct tne tr kc tne ts kc tim
      kbr ts hb hb hb tne tr kc tne ts kc tim wim hb hb tne tr wnot ax3.1 wc hb
      hb tne ts wnot ax3.2 wc wov ax3.2 wct tr ax3.1 exmid a1i tne tr kc tne ts
      kc tim kbr ts kct tr tr tne tr kc tor kbr tne tr kc tne ts kc tim kbr ts
      kct tr tne tr kc tor kbr tne tr kc tne ts kc tim kbr ts kct tne tr kc tne
      ts kc tim kbr ts hb hb hb tne tr kc tne ts kc tim wim hb hb tne tr wnot
      ax3.1 wc hb hb tne ts wnot ax3.2 wc wov ax3.2 wct tr ax3.1 exmid a1i
      ax-cb1 ax3.1 simpr tne tr kc tne ts kc tim kbr ts kct tne tr kc kct tfal
      tr tfal tne tr kc tne ts kc tim kbr tne tr kc ts tne tr kc tne ts kc tim
      kbr tne tr kc kct ts tfal ax3.2 wfal tne ts kc ts tfal tim kbr tne tr kc
      tne ts kc tim kbr tne tr kc kct tne tr kc tne ts kc tim kbr tne tr kc tne
      ts kc hb hb tne tr wnot ax3.1 wc hb hb tne ts wnot ax3.2 wc tne tr kc tne
      ts kc tim kbr hb hb hb tne tr kc tne ts kc tim wim hb hb tne tr wnot
      ax3.1 wc hb hb tne ts wnot ax3.2 wc wov id imp tne ts kc ts tfal tim kbr
      ke kbr tne tr kc tne ts kc tim kbr tne tr kc kct tne ts kc tne tr kc tne
      ts kc tim kbr tne tr kc kct tne tr kc tne ts kc tim kbr tne tr kc tne ts
      kc hb hb tne tr wnot ax3.1 wc hb hb tne ts wnot ax3.2 wc tne tr kc tne ts
      kc tim kbr hb hb hb tne tr kc tne ts kc tim wim hb hb tne tr wnot ax3.1
      wc hb hb tne ts wnot ax3.2 wc wov id imp ax-cb1 ts ax3.2 notval a1i mpbi
      imp an32s tr ax3.1 pm2.21 syl ecase ex wtru adantl ex $.
  $}

  ${
    axmp.1 $e |- S : bool $.
    axmp.2 $e |- T. |= R $.
    axmp.3 $e |- T. |= [ R ==> S ] $.
    $( Rule of Modus Ponens.  The postulated inference rule of propositional
       calculus.  See e.g.  Rule 1 of [Hamilton] p. 73.  (Contributed by Mario
       Carneiro, 10-Oct-2014.) $)
    axmp $p |- T. |= S $=
      kt tr ts axmp.1 axmp.2 axmp.3 mpd $.
  $}

  ${
    $d y R $.  $d y S $.  $d x y al $.
    ax5.1 $e |- R : bool $.
    ax5.2 $e |- S : bool $.
    $( Axiom of Quantified Implication.  Axiom C4 of [Monk2] p. 105.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax5 $p |- T. |= [ ( ! \ x : al . [ R ==> S ] ) ==>
      [ ( ! \ x : al . R ) ==> ( ! \ x : al . S ) ] ] $=
      kt tal hal vx tr ts tim kbr kl kc tal hal vx tr kl kc tal hal vx ts kl kc
      tim kbr tal hal vx tr ts tim kbr kl kc kt tal hal vx tr kl kc tal hal vx
      ts kl kc tim kbr tal hal vx tr ts tim kbr kl kc tal hal vx tr kl kc tal
      hal vx ts kl kc hal vx vy ts tal hal vx tr ts tim kbr kl kc tal hal vx tr
      kl kc kct tal hal vx tr ts tim kbr kl kc tal hal vx tr kl kc kct tr ts
      ax5.2 tal hal vx tr kl kc tal hal vx tr ts tim kbr kl kc tr hal vx tr
      ax5.1 ax4 hal hb ht hb tal hal vx tr ts tim kbr kl hal wal hal hb vx tr
      ts tim kbr hb hb hb tr ts tim wim ax5.1 ax5.2 wov wl wc adantl tal hal vx
      tr ts tim kbr kl kc tal hal vx tr kl kc tr ts tim kbr hal vx tr ts tim
      kbr hb hb hb tr ts tim wim ax5.1 ax5.2 wov ax4 tr tal hal vx tr kl kc hal
      vx tr ax5.1 ax4 ax-cb1 adantr mpd hal vx tal hal vx tr ts tim kbr kl kc
      hal vy tv tal hal vx tr kl kc kt hal hb ht hb tal hal vx tr ts tim kbr kl
      hal wal hal hb vx tr ts tim kbr hb hb hb tr ts tim wim ax5.1 ax5.2 wov wl
      wc hal vy wv tr tal hal vx tr kl kc hal vx tr ax5.1 ax4 ax-cb1 hal hal hb
      ht hb vx hal vx tr ts tim kbr kl hal vy tv tal kt hal wal hal hb vx tr ts
      tim kbr hb hb hb tr ts tim wim ax5.1 ax5.2 wov wl hal vy wv hal hal hb ht
      hb ht vx tal hal vy tv hal wal hal vy wv ax-17 hal hal hb vx tr ts tim
      kbr hal vy tv hb hb hb tr ts tim wim ax5.1 ax5.2 wov hal vy wv ax-hbl1
      hbc hal hal hb ht hb vx hal vx tr kl hal vy tv tal kt hal wal hal hb vx
      tr ax5.1 wl hal vy wv hal hal hb ht hb ht vx tal hal vy tv hal wal hal vy
      wv ax-17 hal hal hb vx tr hal vy tv ax5.1 hal vy wv ax-hbl1 hbc hbct
      alrimi ex wtru adantl ex $.
  $}

  ${
    $d y R $.  $d x y al $.
    ax6.1 $e |- R : bool $.
    $( Axiom of Quantified Negation.  Axiom C5-2 of [Monk2] p. 113.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax6 $p |- T. |= [ ( ~ ( ! \ x : al . R ) ) ==>
      ( ! \ x : al . ( ~ ( ! \ x : al . R ) ) ) ] $=
      hal vx vy tne tal hal vx tr kl kc kc hb hb tne tal hal vx tr kl kc wnot
      hal hb ht hb tal hal vx tr kl hal wal hal hb vx tr ax6.1 wl wc wc hal hb
      hb vx tal hal vx tr kl kc hal vy tv tne kt wnot hal hb ht hb tal hal vx
      tr kl hal wal hal hb vx tr ax6.1 wl wc hal vy wv hal hb hb ht vx tne hal
      vy tv wnot hal vy wv ax-17 hal hal hb ht hb vx hal vx tr kl hal vy tv tal
      kt hal wal hal hb vx tr ax6.1 wl hal vy wv hal hal hb ht hb ht vx tal hal
      vy tv hal wal hal vy wv ax-17 hal hal hb vx tr hal vy tv ax6.1 hal vy wv
      ax-hbl1 hbc hbc isfree $.
  $}

  ${
    $d z R $.  $d x y z al $.
    ax7.1 $e |- R : bool $.
    $( Axiom of Quantifier Commutation.  Axiom scheme C6' in [Megill] p. 448
       (p. 16 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax7 $p |- T. |= [ ( ! \ x : al . ( ! \ y : al . R ) ) ==>
      ( ! \ y : al . ( ! \ x : al . R ) ) ] $=
      kt tal hal vx tal hal vy tr kl kc kl kc tal hal vy tal hal vx tr kl kc kl
      kc tal hal vx tal hal vy tr kl kc kl kc kt tal hal vy tal hal vx tr kl kc
      kl kc hal vy vz tal hal vx tr kl kc tal hal vx tal hal vy tr kl kc kl kc
      hal vx vz tr tal hal vx tal hal vy tr kl kc kl kc tal hal vx tal hal vy
      tr kl kc kl kc tal hal vy tr kl kc tr hal vx tal hal vy tr kl kc hal hb
      ht hb tal hal vy tr kl hal wal hal hb vy tr ax7.1 wl wc ax4 hal vy tr
      ax7.1 ax4 syl hal hal hb ht hb vx hal vx tal hal vy tr kl kc kl hal vz tv
      tal kt hal wal hal hb vx tal hal vy tr kl kc hal hb ht hb tal hal vy tr
      kl hal wal hal hb vy tr ax7.1 wl wc wl hal vz wv hal hal hb ht hb ht vx
      tal hal vz tv hal wal hal vz wv ax-17 hal hal hb vx tal hal vy tr kl kc
      hal vz tv hal hb ht hb tal hal vy tr kl hal wal hal hb vy tr ax7.1 wl wc
      hal vz wv ax-hbl1 hbc alrimi hal hal hb ht hb vy hal vx tal hal vy tr kl
      kc kl hal vz tv tal kt hal wal hal hb vx tal hal vy tr kl kc hal hb ht hb
      tal hal vy tr kl hal wal hal hb vy tr ax7.1 wl wc wl hal vz wv hal hal hb
      ht hb ht vy tal hal vz tv hal wal hal vz wv ax-17 hal hal hb vy vx tal
      hal vy tr kl kc hal vz tv kt hal hb ht hb tal hal vy tr kl hal wal hal hb
      vy tr ax7.1 wl wc hal vz wv hal hal hb ht hb vy hal vy tr kl hal vz tv
      tal kt hal wal hal hb vy tr ax7.1 wl hal vz wv hal hal hb ht hb ht vy tal
      hal vz tv hal wal hal vz wv ax-17 hal hal hb vy tr hal vz tv ax7.1 hal vz
      wv ax-hbl1 hbc hbl hbc alrimi wtru adantl ex $.
  $}

  ${
    $d x al $.
    axgen.1 $e |- T. |= R $.
    $( Rule of Generalization.  See e.g.  Rule 2 of [Hamilton] p. 74.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    axgen $p |- T. |= ( ! \ x : al . R ) $=
      hal vx tr kt axgen.1 alrimiv $.
  $}

  ${
    ax8.1 $e |- A : al $.
    ax8.2 $e |- B : al $.
    ax8.3 $e |- C : al $.
    $( Axiom of Equality.  Axiom scheme C8' in [Megill] p. 448 (p. 16 of the
       preprint).  Also appears as Axiom C7 of [Monk2] p. 105.  (Contributed by
       Mario Carneiro, 10-Oct-2014.) $)
    ax8 $p |- T. |= [ [ A = B ] ==> [ [ A = C ] ==> [ B = C ] ] ] $=
      kt ta tb ke kbr ta tc ke kbr tb tc ke kbr tim kbr ta tb ke kbr kt ta tc
      ke kbr tb tc ke kbr tim kbr ta tb ke kbr ta tc ke kbr tb tc ke kbr hal tb
      ta tc ta tb ke kbr ta tc ke kbr kct ax8.2 hal ta tb ta tb ke kbr ta tc ke
      kbr kct ax8.1 ta tb ke kbr ta tc ke kbr hal ta tb ax8.1 ax8.2 weqi hal ta
      tc ax8.1 ax8.3 weqi simpl eqcomi ta tb ke kbr ta tc ke kbr hal ta tb
      ax8.1 ax8.2 weqi hal ta tc ax8.1 ax8.3 weqi simpr eqtri ex wtru adantl ex
      $.
  $}

  ${
    $d y A $.  $d x y al $.
    ax9.1 $e |- A : al $.
    $( Axiom of Equality.  Axiom scheme C8' in [Megill] p. 448 (p. 16 of the
       preprint).  Also appears as Axiom C7 of [Monk2] p. 105.  (Contributed by
       Mario Carneiro, 10-Oct-2014.) $)
    ax9 $p |- T. |= ( ~ ( ! \ x : al . ( ~ [ x : al = A ] ) ) ) $=
      tne tne tex hal vx hal vx tv ta ke kbr kl kc kc kc tne tal hal vx tne hal
      vx tv ta ke kbr kc kl kc kc kt kt tex hal vx hal vx tv ta ke kbr kl kc
      tne tne tex hal vx hal vx tv ta ke kbr kl kc kc kc hal vx vy tex hal vx
      hal vx tv ta ke kbr kl kc tex hal vx hal vx tv ta ke kbr kl kc ta hal vx
      tv ta ke kbr kt hal vx hal vx tv ta ke kbr hal hal vx tv ta hal vx wv
      ax9.1 weqi 19.8a hal hal hb ht hb vx hal vx hal vx tv ta ke kbr kl hal vy
      tv tex kt hal wex hal hb vx hal vx tv ta ke kbr hal hal vx tv ta hal vx
      wv ax9.1 weqi wl hal vy wv hal hal hb ht hb ht vx tex hal vy tv hal wex
      hal vy wv ax-17 hal hal hb vx hal vx tv ta ke kbr hal vy tv hal hal vx tv
      ta hal vx wv ax9.1 weqi hal vy wv ax-hbl1 hbc hal hb vx kt hal vy tv wtru
      hal vy wv ax-17 hb tex hal vx hal vx tv ta ke kbr kl kc hal vx tv ta ke
      kbr hal hal vx tv ta hal vx wv ax9.1 weqi hal hb ht hb tex hal vx hal vx
      tv ta ke kbr kl hal wex hal hb vx hal vx tv ta ke kbr hal hal vx tv ta
      hal vx wv ax9.1 weqi wl wc eqid hb kt hal vx tv ta ke kbr hal vx tv ta ke
      kbr wtru hal vx tv ta ke kbr hal vx tv ta ke kbr hal vx tv ta ke kbr hal
      hal vx tv ta hal vx wv ax9.1 weqi id eqtru eqcomi ax-inst tex hal vx hal
      vx tv ta ke kbr kl kc hal hb ht hb tex hal vx hal vx tv ta ke kbr kl hal
      wex hal hb vx hal vx tv ta ke kbr hal hal vx tv ta hal vx wv ax9.1 weqi
      wl wc notnot1 syl hb hb tal hal vx tne hal vx tv ta ke kbr kc kl kc tne
      tex hal vx hal vx tv ta ke kbr kl kc kc tne kt wnot hal hb ht hb tal hal
      vx tne hal vx tv ta ke kbr kc kl hal wal hal hb vx tne hal vx tv ta ke
      kbr kc hb hb tne hal vx tv ta ke kbr wnot hal hal vx tv ta hal vx wv
      ax9.1 weqi wc wl wc hal vx hal vx tv ta ke kbr hal hal vx tv ta hal vx wv
      ax9.1 weqi alnex ceq2 mpbir $.
  $}

  ${
    $d x y z al $.
    $( Axiom of Quantifier Substitution.  Appears as Lemma L12 in [Megill]
       p. 445 (p. 12 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax10 $p |- T. |= [ ( ! \ x : al . [ x : al = y : al ] ) ==>
      ( ! \ y : al . [ y : al = x : al ] ) ] $=
      kt tal hal vx hal vx tv hal vy tv ke kbr kl kc tal hal vy hal vy tv hal
      vx tv ke kbr kl kc tal hal vx hal vx tv hal vy tv ke kbr kl kc kt tal hal
      vy hal vy tv hal vx tv ke kbr kl kc tal hal vz hal vz tv hal vx tv ke kbr
      kl kc tal hal vy hal vy tv hal vx tv ke kbr kl kc tal hal vx hal vx tv
      hal vy tv ke kbr kl kc hal vz hal vz tv hal vx tv ke kbr tal hal vx hal
      vx tv hal vy tv ke kbr kl kc hal hal vz tv hal vy tv hal vx tv tal hal vx
      hal vx tv hal vy tv ke kbr kl kc hal vz wv hal vx hal vx tv hal vy tv ke
      kbr hal vz tv hal vz tv hal vy tv ke kbr hal hal vx tv hal vy tv hal vx
      wv hal vy wv weqi hal vz wv hal hal hb hal vx tv hal vy tv hal vz tv ke
      hal vx tv hal vz tv ke kbr hal weq hal vx wv hal vy wv hal vx tv hal vz
      tv ke kbr hal hal hb hal vx tv hal vz tv ke hal weq hal vx wv hal vz wv
      wov id oveq1 cla4v hal hal vx tv hal vy tv tal hal vx hal vx tv hal vy tv
      ke kbr kl kc hal vx wv hal vx hal vx tv hal vy tv ke kbr hal hal vx tv
      hal vy tv hal vx wv hal vy wv weqi ax4 eqcomi eqtri alrimiv tal hal vy
      hal vy tv hal vx tv ke kbr kl kc tal hal vz hal vz tv hal vx tv ke kbr kl
      kc ke kbr tal hal vx hal vx tv hal vy tv ke kbr kl kc hal hb ht hb tal
      hal vx hal vx tv hal vy tv ke kbr kl hal wal hal hb vx hal vx tv hal vy
      tv ke kbr hal hal vx tv hal vy tv hal vx wv hal vy wv weqi wl wc hal hb
      ht hb hal vy hal vy tv hal vx tv ke kbr kl hal vz hal vz tv hal vx tv ke
      kbr kl tal kt hal wal hal hb vy hal vy tv hal vx tv ke kbr hal hal vy tv
      hal vx tv hal vy wv hal vx wv weqi wl hal hb vy vz hal vy tv hal vx tv ke
      kbr hal vz tv hal vx tv ke kbr hal hal vy tv hal vx tv hal vy wv hal vx
      wv weqi hal hal hb hal vy tv hal vx tv hal vz tv ke hal vy tv hal vz tv
      ke kbr hal weq hal vy wv hal vx wv hal vy tv hal vz tv ke kbr hal hal vy
      tv hal vz tv hal vy wv hal vz wv weqi id oveq1 cbv ceq2 a1i mpbir wtru
      adantl ex $.
  $}

  ${
    $d x A $.  $d x y al $.
    ax11.1 $e |- A : bool $.
    $( Axiom of Variable Substitution.  It is based on Lemma 16 of [Tarski]
       p. 70 and Axiom C8 of [Monk2] p. 105, from which it can be proved by
       cases.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax11 $p |- T. |= [ [ x : al = y : al ] ==> [ ( ! \ y : al . A ) ==>
      ( ! \ x : al . [ [ x : al = y : al ] ==> A ] ) ] ] $=
      kt hal vx tv hal vy tv ke kbr tal hal vy ta kl kc tal hal vx hal vx tv
      hal vy tv ke kbr ta tim kbr kl kc tim kbr kt hal vx tv hal vy tv ke kbr
      kct tal hal vy ta kl kc tal hal vx hal vx tv hal vy tv ke kbr ta tim kbr
      kl kc tal hal vy ta kl kc kt hal vx tv hal vy tv ke kbr kct tal hal vx
      hal vx tv hal vy tv ke kbr ta tim kbr kl kc tal hal vy ta kl kc tal hal
      vx hal vy ta kl hal vx tv kc kl kc tal hal vx hal vx tv hal vy tv ke kbr
      ta tim kbr kl kc tal hal vy ta kl kc tal hal vx hal vy ta kl hal vx tv kc
      kl kc tal hal vy ta kl kc tal hal vy ta kl kc hal hb ht hb tal hal vy ta
      kl hal wal hal hb vy ta ax11.1 wl wc id tal hal vx hal vy ta kl hal vx tv
      kc kl kc tal hal vy ta kl kc ke kbr tal hal vy ta kl kc hal hb ht hb tal
      hal vy ta kl hal wal hal hb vy ta ax11.1 wl wc hal hb ht hb hal vx hal vy
      ta kl hal vx tv kc kl hal vy ta kl tal kt hal wal hal hb vx hal vy ta kl
      hal vx tv kc hal hb hal vy ta kl hal vx tv hal hb vy ta ax11.1 wl hal vx
      wv wc wl hal hb vx hal vy ta kl hal hb vy ta ax11.1 wl eta ceq2 a1i mpbir
      tal hal vx hal vy ta kl hal vx tv kc kl kc tal hal vx hal vy ta kl hal vx
      tv kc kl kc tal hal vx hal vx tv hal vy tv ke kbr ta tim kbr kl kc hal hb
      ht hb tal hal vx hal vx tv hal vy tv ke kbr ta tim kbr kl hal wal hal hb
      vx hal vx tv hal vy tv ke kbr ta tim kbr hb hb hb hal vx tv hal vy tv ke
      kbr ta tim wim hal hal vx tv hal vy tv hal vx wv hal vy wv weqi ax11.1
      wov wl wc tal hal vx hal vy ta kl hal vx tv kc kl kc hal hb ht hb tal hal
      vx hal vy ta kl hal vx tv kc kl hal wal hal hb vx hal vy ta kl hal vx tv
      kc hal hb hal vy ta kl hal vx tv hal hb vy ta ax11.1 wl hal vx wv wc wl
      wc id tal hal vx hal vy ta kl hal vx tv kc kl kc tal hal vx hal vx tv hal
      vy tv ke kbr ta tim kbr kl kc tim kbr tal hal vx hal vy ta kl hal vx tv
      kc kl kc hal hb ht hb tal hal vx hal vy ta kl hal vx tv kc kl hal wal hal
      hb vx hal vy ta kl hal vx tv kc hal hb hal vy ta kl hal vx tv hal hb vy
      ta ax11.1 wl hal vx wv wc wl wc kt tal hal vx hal vy ta kl hal vx tv kc
      hal vx tv hal vy tv ke kbr ta tim kbr tim kbr kl kc tal hal vx hal vy ta
      kl hal vx tv kc kl kc tal hal vx hal vx tv hal vy tv ke kbr ta tim kbr kl
      kc tim kbr hb hb hb tal hal vx hal vy ta kl hal vx tv kc kl kc tal hal vx
      hal vx tv hal vy tv ke kbr ta tim kbr kl kc tim wim tal hal vx hal vy ta
      kl hal vx tv kc kl kc hal vx tv hal vy tv ke kbr tal hal vy ta kl kc kct
      tal hal vy ta kl kc tal hal vx hal vy ta kl hal vx tv kc kl kc hal vx tv
      hal vy tv ke kbr tal hal vy ta kl kc kct hal vx tv hal vy tv ke kbr tal
      hal vy ta kl kc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi hal hb
      ht hb tal hal vy ta kl hal wal hal hb vy ta ax11.1 wl wc simpr tal hal vx
      hal vy ta kl hal vx tv kc kl kc tal hal vy ta kl kc ke kbr hal vx tv hal
      vy tv ke kbr tal hal vy ta kl kc kct tal hal vy ta kl kc hal vx tv hal vy
      tv ke kbr tal hal vy ta kl kc kct hal vx tv hal vy tv ke kbr tal hal vy
      ta kl kc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi hal hb ht hb
      tal hal vy ta kl hal wal hal hb vy ta ax11.1 wl wc simpr ax-cb1 hal hb ht
      hb hal vx hal vy ta kl hal vx tv kc kl hal vy ta kl tal kt hal wal hal hb
      vx hal vy ta kl hal vx tv kc hal hb hal vy ta kl hal vx tv hal hb vy ta
      ax11.1 wl hal vx wv wc wl hal hb vx hal vy ta kl hal hb vy ta ax11.1 wl
      eta ceq2 a1i mpbir ax-cb2 hal hb ht hb tal hal vx hal vx tv hal vy tv ke
      kbr ta tim kbr kl hal wal hal hb vx hal vx tv hal vy tv ke kbr ta tim kbr
      hb hb hb hal vx tv hal vy tv ke kbr ta tim wim hal hal vx tv hal vy tv
      hal vx wv hal vy wv weqi ax11.1 wov wl wc wov hal vx hal vy ta kl hal vx
      tv kc hal vx tv hal vy tv ke kbr ta tim kbr tim kbr kt kt hal vy ta kl
      hal vx tv kc hal vx tv hal vy tv ke kbr ta tim kbr hal vy ta kl hal vx tv
      kc kt hal vx tv hal vy tv ke kbr ta tim kbr hal vy ta kl hal vx tv kc hal
      vx tv hal vy tv ke kbr ta hal vy ta kl hal vx tv kc ta hal vy ta kl hal
      vx tv kc hal vx tv hal vy tv ke kbr kct hal vy ta kl hal vx tv kc hal vx
      tv hal vy tv ke kbr hal hb hal vy ta kl hal vx tv hal hb vy ta ax11.1 wl
      hal vx wv wc hal hal vx tv hal vy tv hal vx wv hal vy wv weqi simpl hb
      hal vy ta kl hal vx tv kc hal vy ta kl hal vy tv kc ta hal vy ta kl hal
      vx tv kc hal vx tv hal vy tv ke kbr kct hal hb hal vy ta kl hal vx tv hal
      hb vy ta ax11.1 wl hal vx wv wc hal hb hal vx tv hal vy tv hal vy ta kl
      hal vy ta kl hal vx tv kc hal vx tv hal vy tv ke kbr kct hal hb vy ta
      ax11.1 wl hal vx wv hal vy ta kl hal vx tv kc hal vx tv hal vy tv ke kbr
      hal hb hal vy ta kl hal vx tv hal hb vy ta ax11.1 wl hal vx wv wc hal hal
      vx tv hal vy tv hal vx wv hal vy wv weqi simpr ceq2 hal vy ta kl hal vy
      tv kc ta ke kbr hal vy ta kl hal vx tv kc hal vx tv hal vy tv ke kbr kct
      hal vy ta kl hal vx tv kc hal vx tv hal vy tv ke kbr hal hb hal vy ta kl
      hal vx tv hal hb vy ta ax11.1 wl hal vx wv wc hal hal vx tv hal vy tv hal
      vx wv hal vy wv weqi wct hal hb vy ta ax11.1 beta a1i eqtri mpbi ex wtru
      adantl ex alrimiv hal vx hal vy ta kl hal vx tv kc hal vx tv hal vy tv ke
      kbr ta tim kbr hal hb hal vy ta kl hal vx tv hal hb vy ta ax11.1 wl hal
      vx wv wc hb hb hb hal vx tv hal vy tv ke kbr ta tim wim hal hal vx tv hal
      vy tv hal vx wv hal vy wv weqi ax11.1 wov ax5 mpd a1i mpd syl kt hal vx
      tv hal vy tv ke kbr wtru hal hal vx tv hal vy tv hal vx wv hal vy wv weqi
      wct adantl ex ex $.
  $}

  ${
    $d p x z $.  $d p y z $.  $d p z al $.
    $( Axiom of Quantifier Introduction.  Axiom scheme C9' in [Megill] p. 448
       (p. 16 of the preprint).  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    ax12 $p |- T. |=
      [ ( ~ ( ! \ z : al . [ z : al = x : al ] ) ) ==>
        [ ( ~ ( ! \ z : al . [ z : al = y : al ] ) ) ==>
    [ [ x : al = y : al ] ==> ( ! \ z : al . [ x : al = y : al ] ) ] ] ] $=
      kt tne tal hal vz hal vz tv hal vx tv ke kbr kl kc kc tne tal hal vz hal
      vz tv hal vy tv ke kbr kl kc kc hal vx tv hal vy tv ke kbr tal hal vz hal
      vx tv hal vy tv ke kbr kl kc tim kbr tim kbr kt tne tal hal vz hal vz tv
      hal vx tv ke kbr kl kc kc tne tal hal vz hal vz tv hal vy tv ke kbr kl kc
      kc hal vx tv hal vy tv ke kbr tal hal vz hal vx tv hal vy tv ke kbr kl kc
      tim kbr tim kbr kt tne tal hal vz hal vz tv hal vy tv ke kbr kl kc kc hal
      vx tv hal vy tv ke kbr tal hal vz hal vx tv hal vy tv ke kbr kl kc tim
      kbr kt tne tal hal vz hal vz tv hal vy tv ke kbr kl kc kc hal vx tv hal
      vy tv ke kbr tal hal vz hal vx tv hal vy tv ke kbr kl kc tim kbr hal vz
      vp hal vx tv hal vy tv ke kbr hal hal vx tv hal vy tv hal vx wv hal vy wv
      weqi hal hb vz hal vx tv hal vy tv ke kbr hal vp tv hal hal vx tv hal vy
      tv hal vx wv hal vy wv weqi hal vp wv ax-17 isfree hb hb tne tal hal vz
      hal vz tv hal vy tv ke kbr kl kc wnot hal hb ht hb tal hal vz hal vz tv
      hal vy tv ke kbr kl hal wal hal hb vz hal vz tv hal vy tv ke kbr hal hal
      vz tv hal vy tv hal vz wv hal vy wv weqi wl wc wc adantr ex hb hb tne tal
      hal vz hal vz tv hal vx tv ke kbr kl kc wnot hal hb ht hb tal hal vz hal
      vz tv hal vx tv ke kbr kl hal wal hal hb vz hal vz tv hal vx tv ke kbr
      hal hal vz tv hal vx tv hal vz wv hal vx wv weqi wl wc wc adantr ex $.
  $}

  ${
    ax13.1 $e |- A : al $.
    ax13.2 $e |- B : al $.
    ax13.3 $e |- C : ( al -> bool ) $.
    $( Axiom of Equality.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the
       preprint).  It is a special case of Axiom B8 (p. 75) of system S2 of
       [Tarski] p. 77.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax13 $p |- T. |= [ [ A = B ] ==> [ ( C A ) ==> ( C B ) ] ] $=
      kt ta tb ke kbr tc ta kc tc tb kc tim kbr kt ta tb ke kbr kct tc ta kc tc
      tb kc tc ta kc tc tb kc kt ta tb ke kbr kct tc ta kc kct kt ta tb ke kbr
      kct tc ta kc kt ta tb ke kbr wtru hal ta tb ax13.1 ax13.2 weqi wct hal hb
      tc ta ax13.3 ax13.1 wc simpr kt ta tb ke kbr kct tc ta kc tc ta kc tc tb
      kc ke kbr hal hb ta tb tc kt ta tb ke kbr kct ax13.3 ax13.1 kt ta tb ke
      kbr wtru hal ta tb ax13.1 ax13.2 weqi simpr ceq2 hal hb tc ta ax13.3
      ax13.1 wc adantr mpbi ex ex $.
  $}

  ${
    ax14.1 $e |- A : ( al -> bool ) $.
    ax14.2 $e |- B : ( al -> bool ) $.
    ax14.3 $e |- C : al $.
    $( Axiom of Equality.  Axiom scheme C12' in [Megill] p. 448 (p. 16 of the
       preprint).  It is a special case of Axiom B8 (p. 75) of system S2 of
       [Tarski] p. 77.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax14 $p |- T. |= [ [ A = B ] ==> [ ( A C ) ==> ( B C ) ] ] $=
      kt ta tb ke kbr ta tc kc tb tc kc tim kbr kt ta tb ke kbr kct ta tc kc tb
      tc kc ta tc kc tb tc kc kt ta tb ke kbr kct ta tc kc kct kt ta tb ke kbr
      kct ta tc kc kt ta tb ke kbr wtru hal hb ht ta tb ax14.1 ax14.2 weqi wct
      hal hb ta tc ax14.1 ax14.3 wc simpr kt ta tb ke kbr kct ta tc kc ta tc kc
      tb tc kc ke kbr hal hb tc ta kt ta tb ke kbr kct tb ax14.1 ax14.3 kt ta
      tb ke kbr wtru hal hb ht ta tb ax14.1 ax14.2 weqi simpr ceq1 hal hb ta tc
      ax14.1 ax14.3 wc adantr mpbi ex ex $.
  $}

  ${
    $d x y A $.  $d x y al $.
    ax17m.1 $e |- A : bool $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.  (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    ax17m $p |- T. |= [ A ==> ( ! \ x : al . A ) ] $=
      hal vx vy ta ax17m.1 hal hb vx ta hal vy tv ax17m.1 hal vy wv ax-17
      isfree $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y al $.
    axext.1 $e |- A : ( al -> bool ) $.
    axext.2 $e |- B : ( al -> bool ) $.
    $( Axiom of Extensionality.  An axiom of Zermelo-Fraenkel set theory.  It
       states that two sets are identical if they contain the same elements.
       Axiom Ext of [BellMachover] p. 461.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    axext $p |- T. |=
      [ ( ! \ x : al . [ ( A x : al ) = ( B x : al ) ] ) ==> [ A = B ] ] $=
      kt tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl kc ta tb ke kbr
      tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl kc kt ta tb ke kbr
      hal hb ht hal vx ta hal vx tv kc kl hal vx tb hal vx tv kc kl tal hal vx
      ta hal vx tv kc tb hal vx tv kc ke kbr kl kc ta tb hal hb vx ta hal vx tv
      kc hal hb ta hal vx tv axext.1 hal vx wv wc wl hal hb vx vy ta hal vx tv
      kc tb hal vx tv kc tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl
      kc hal hb ta hal vx tv axext.1 hal vx wv wc hal vx ta hal vx tv kc tb hal
      vx tv kc ke kbr hb ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv
      axext.1 hal vx wv wc hal hb tb hal vx tv axext.2 hal vx wv wc weqi ax4
      hal hal hb ht hb vx hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl hal
      vy tv tal kt hal wal hal hb vx ta hal vx tv kc tb hal vx tv kc ke kbr hb
      ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv axext.1 hal vx wv wc
      hal hb tb hal vx tv axext.2 hal vx wv wc weqi wl hal vy wv hal hal hb ht
      hb ht vx tal hal vy tv hal wal hal vy wv ax-17 hal hal hb vx ta hal vx tv
      kc tb hal vx tv kc ke kbr hal vy tv hb ta hal vx tv kc tb hal vx tv kc
      hal hb ta hal vx tv axext.1 hal vx wv wc hal hb tb hal vx tv axext.2 hal
      vx wv wc weqi hal vy wv ax-hbl1 hbc leqf hal vx ta hal vx tv kc kl ta ke
      kbr tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl kc hal vx ta hal
      vx tv kc kl hal vx tb hal vx tv kc kl ke kbr tal hal vx ta hal vx tv kc
      tb hal vx tv kc ke kbr kl kc hal hb vx vy ta hal vx tv kc tb hal vx tv kc
      tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl kc hal hb ta hal vx
      tv axext.1 hal vx wv wc hal vx ta hal vx tv kc tb hal vx tv kc ke kbr hb
      ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv axext.1 hal vx wv wc
      hal hb tb hal vx tv axext.2 hal vx wv wc weqi ax4 hal hal hb ht hb vx hal
      vx ta hal vx tv kc tb hal vx tv kc ke kbr kl hal vy tv tal kt hal wal hal
      hb vx ta hal vx tv kc tb hal vx tv kc ke kbr hb ta hal vx tv kc tb hal vx
      tv kc hal hb ta hal vx tv axext.1 hal vx wv wc hal hb tb hal vx tv
      axext.2 hal vx wv wc weqi wl hal vy wv hal hal hb ht hb ht vx tal hal vy
      tv hal wal hal vy wv ax-17 hal hal hb vx ta hal vx tv kc tb hal vx tv kc
      ke kbr hal vy tv hb ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv
      axext.1 hal vx wv wc hal hb tb hal vx tv axext.2 hal vx wv wc weqi hal vy
      wv ax-hbl1 hbc leqf ax-cb1 hal hb vx ta axext.1 eta a1i hal vx tb hal vx
      tv kc kl tb ke kbr tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl
      kc hal vx ta hal vx tv kc kl hal vx tb hal vx tv kc kl ke kbr tal hal vx
      ta hal vx tv kc tb hal vx tv kc ke kbr kl kc hal hb vx vy ta hal vx tv kc
      tb hal vx tv kc tal hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl kc
      hal hb ta hal vx tv axext.1 hal vx wv wc hal vx ta hal vx tv kc tb hal vx
      tv kc ke kbr hb ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv
      axext.1 hal vx wv wc hal hb tb hal vx tv axext.2 hal vx wv wc weqi ax4
      hal hal hb ht hb vx hal vx ta hal vx tv kc tb hal vx tv kc ke kbr kl hal
      vy tv tal kt hal wal hal hb vx ta hal vx tv kc tb hal vx tv kc ke kbr hb
      ta hal vx tv kc tb hal vx tv kc hal hb ta hal vx tv axext.1 hal vx wv wc
      hal hb tb hal vx tv axext.2 hal vx wv wc weqi wl hal vy wv hal hal hb ht
      hb ht vx tal hal vy tv hal wal hal vy wv ax-17 hal hal hb vx ta hal vx tv
      kc tb hal vx tv kc ke kbr hal vy tv hb ta hal vx tv kc tb hal vx tv kc
      hal hb ta hal vx tv axext.1 hal vx wv wc hal hb tb hal vx tv axext.2 hal
      vx wv wc weqi hal vy wv ax-hbl1 hbc leqf ax-cb1 hal hb vx tb axext.2 eta
      a1i 3eqtr3i wtru adantl ex $.
  $}

  ${
    $d f A $.  $d f y B $.  $d f y al $.  $d f x y be $.  $d f y z be $.
    axrep.1 $e |- A : bool $.
    axrep.2 $e |- B : ( al -> bool ) $.
    $( Axiom of Replacement.  An axiom scheme of Zermelo-Fraenkel set theory.
       Axiom 5 of [TakeutiZaring] p. 19.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    axrep $p |- T. |= [ ( ! \ x : al . ( ? \ y : be . ( ! \ z : be .
      [ ( ! \ y : be . A ) ==> [ z : be = y : be ] ] ) ) ) ==>
      ( ? \ y : ( be -> bool ) .
        ( ! \ z : be . [ ( y : ( be -> bool ) z : be ) =
          ( ? \ x : al . [ ( B x : al ) /\ ( ! \ y : be . A ) ] ) ] ) ) ] $=
      kt tal hal vx tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy
      tv ke kbr tim kbr kl kc kl kc kl kc tex hbe hb ht vy tal hbe vz hbe hb ht
      vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      kl kc ke kbr kl kc kl kc tal hal vx tex hbe vy tal hbe vz tal hbe vy ta
      kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl kc kl kc kl kc kt tex hbe hb
      ht vy tal hbe vz hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc kl kc tal hal vx tex hbe
      vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl
      kc kl kc kl kc hbe hb ht vy tal hbe vz hbe hb ht vy tv hbe vz tv kc tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc kl
      hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl kc
      tex hbe hb ht vy tal hbe vz hbe hb ht vy tv hbe vz tv kc tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc kl kc tal hbe
      vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal
      vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc hbe hb
      ht vy tal hbe vz hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc kl hbe vz tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl kc tal hal vx tex hbe
      vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl
      kc kl kc kl kc tal hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      kc ke kbr kl kc tal hal vx tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe
      vz tv hbe vy tv ke kbr tim kbr kl kc kl kc kl kc hal hb ht hb tal hal vx
      tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim
      kbr kl kc kl kc kl hal wal hal hb vx tex hbe vy tal hbe vz tal hbe vy ta
      kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl kc kl kc hbe hb ht hb tex hbe
      vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl
      kc kl hbe wex hbe hb vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy
      tv ke kbr tim kbr kl kc hbe hb ht hb tal hbe vz tal hbe vy ta kl kc hbe
      vz tv hbe vy tv ke kbr tim kbr kl hbe wal hbe hb vz tal hbe vy ta kl kc
      hbe vz tv hbe vy tv ke kbr tim kbr hb hb hb tal hbe vy ta kl kc hbe vz tv
      hbe vy tv ke kbr tim wim hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy
      ta axrep.1 wl wc hbe hbe vz tv hbe vy tv hbe vz wv hbe vy wv weqi wov wl
      wc wl wc wl wc hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke
      kbr kt hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kt
      wtru hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      kl hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb
      tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2
      hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1
      wl wc wov wl wc eqid alrimiv a1i hbe hb ht vy tal hbe vz hbe hb ht vy tv
      hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc
      ke kbr kl kc kl hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc kl kc tal hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      kc ke kbr kl kc ke kbr tal hal vx tex hbe vy tal hbe vz tal hbe vy ta kl
      kc hbe vz tv hbe vy tv ke kbr tim kbr kl kc kl kc kl kc tal hbe vz tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl kc tal hal vx
      tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim
      kbr kl kc kl kc kl kc tal hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta
      kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc ke kbr kl kc tal hal vx tex hbe vy tal hbe vz tal hbe vy ta kl
      kc hbe vz tv hbe vy tv ke kbr tim kbr kl kc kl kc kl kc hal hb ht hb tal
      hal vx tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke
      kbr tim kbr kl kc kl kc kl hal wal hal hb vx tex hbe vy tal hbe vz tal
      hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl kc kl kc hbe hb ht
      hb tex hbe vy tal hbe vz tal hbe vy ta kl kc hbe vz tv hbe vy tv ke kbr
      tim kbr kl kc kl hbe wex hbe hb vy tal hbe vz tal hbe vy ta kl kc hbe vz
      tv hbe vy tv ke kbr tim kbr kl kc hbe hb ht hb tal hbe vz tal hbe vy ta
      kl kc hbe vz tv hbe vy tv ke kbr tim kbr kl hbe wal hbe hb vz tal hbe vy
      ta kl kc hbe vz tv hbe vy tv ke kbr tim kbr hb hb hb tal hbe vy ta kl kc
      hbe vz tv hbe vy tv ke kbr tim wim hbe hb ht hb tal hbe vy ta kl hbe wal
      hbe hb vy ta axrep.1 wl wc hbe hbe vz tv hbe vy tv hbe vz wv hbe vy wv
      weqi wov wl wc wl wc wl wc hbe vz tex hal vx tb hal vx tv kc tal hbe vy
      ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc ke kbr kt hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc kt wtru hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta
      kl kc tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb
      hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe
      hb vy ta axrep.1 wl wc wov wl wc eqid alrimiv a1i ax-cb1 hbe hb ht hb vy
      vf tal hbe vz hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr kl kc tal hbe vz tex hal vx tb hal
      vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr kl kc hbe vz tex hal vx tb hal vx tv
      kc tal hbe vy ta kl kc tan kbr kl kc kl hbe hb ht hb tal hbe vz hbe hb ht
      vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      kl kc ke kbr kl hbe wal hbe hb vz hbe hb ht vy tv hbe vz tv kc tex hal vx
      tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr hb hbe hb ht vy
      tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      kc hbe hb hbe hb ht vy tv hbe vz tv hbe hb ht vy wv hbe vz wv wc hal hb
      ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex
      hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx
      tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv
      wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov
      wl wc weqi wl wc hbe hb vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv
      axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta
      axrep.1 wl wc wov wl wc wl hbe hb ht hb hbe vz hbe hb ht vy tv hbe vz tv
      kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl
      hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl tal
      hbe hb ht vy tv hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc kl ke kbr hbe wal hbe hb vz hbe hb ht vy tv hbe vz tv kc tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr hb hbe hb
      ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc hbe hb hbe hb ht vy tv hbe vz tv hbe hb ht vy wv hbe vz wv wc
      hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb
      hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal
      vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc
      wov wl wc weqi wl hbe hb vz vf hbe hb ht vy tv hbe vz tv kc tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr tex hal vx tb hal
      vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr hbe hb ht vy tv hbe vz tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke kbr hb hbe hb ht vy
      tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      kc hbe hb hbe hb ht vy tv hbe vz tv hbe hb ht vy wv hbe vz wv wc hal hb
      ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex
      hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx
      tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv
      wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov
      wl wc weqi hb hb hb hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv
      kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal hbe
      vy ta kl kc tan kbr kl kc ke hbe hb ht vy tv hbe vz tex hal vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke kbr hb weq hbe hb hbe hb ht
      vy tv hbe vz tv hbe hb ht vy wv hbe vz wv wc hal hb ht hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta
      kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal
      hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc hb hbe hb ht vy
      tv hbe vz tv kc hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr kl kc kl hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc hbe hb ht vy tv hbe vz tex hal vx tb hal vx tv kc tal hbe
      vy ta kl kc tan kbr kl kc kl ke kbr hbe hb hbe hb ht vy tv hbe vz tv hbe
      hb ht vy wv hbe vz wv wc hbe hb hbe vz tv hbe hb ht vy tv hbe hb ht vy tv
      hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke
      kbr hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc
      kl hbe hb ht vy wv hbe vz wv hbe hb ht vy tv hbe vz tex hal vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke kbr hbe hb ht hbe hb ht vy
      tv hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl
      hbe hb ht vy wv hbe hb vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv
      axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta
      axrep.1 wl wc wov wl wc wl weqi id ceq1 hbe vz tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl kc kl hbe vz tv kc tex hal vx tb hal vx tv
      kc tal hbe vy ta kl kc tan kbr kl kc ke kbr hbe hb ht vy tv hbe vz tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke kbr hbe hb
      ht hbe hb ht vy tv hbe vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl kc kl hbe hb ht vy wv hbe hb vz tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc hal hb ht hb tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy
      ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal
      hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe
      wal hbe hb vy ta axrep.1 wl wc wov wl wc wl weqi hbe hb vz tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc hal hb ht hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta
      kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal
      hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc beta a1i eqtri
      oveq1 hbe hbe hb ht hbe hb ht hb vz hbe hb ht vy tv hbe vf tv hbe vz tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl ke kt hbe hb
      ht weq hbe hb ht vy wv hbe vf wv hbe hb vz tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc hal hb ht hb tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy
      ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal
      hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe
      wal hbe hb vy ta axrep.1 wl wc wov wl wc wl hbe hb hb hb ht ht vz ke hbe
      vf tv hb weq hbe vf wv ax-17 hbe hbe hb ht vz hbe hb ht vy tv hbe vf tv
      hbe hb ht vy wv hbe vf wv ax-17 hbe hbe hb vz tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl kc hbe vf tv hal hb ht hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta
      kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal
      hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc hbe vf wv
      ax-hbl1 hbov leqf ceq2 hbe hb ht hbe hb ht hb vy hbe vz tex hal vx tb hal
      vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr kl hbe hb ht vf tv tal kt hbe wal
      hbe hb vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc
      tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr hb
      tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx
      tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc hal hb ht hb tex hal vx
      tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal
      vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy
      ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb
      tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc hal hb ht
      hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal
      hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv
      kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc
      hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl
      wc weqi wl hbe hb ht vf wv hbe hb ht hbe hb ht hb ht vy tal hbe hb ht vf
      tv hbe wal hbe hb ht vf wv ax-17 hbe hb ht hbe hb vy vz tex hal vx tb hal
      vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr hbe hb ht vf tv kt hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl kc hal hb ht hb tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe
      vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan
      hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl
      hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc hal hb ht hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta
      kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal
      hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc weqi hbe hb ht
      vf wv hbe hb ht hb hb hb vy tex hal vx tb hal vx tv kc tal hbe vy ta kl
      kc tan kbr kl kc hbe hb ht vf tv tex hal vx tb hal vx tv kc tal hbe vy ta
      kl kc tan kbr kl kc ke kt hb weq hal hb ht hb tex hal vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe
      vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan
      hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl
      hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc hbe hb ht vf wv hal hb ht hb
      tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb
      vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc
      tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe
      hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc
      hbe hb ht hga hga hb ht ht vy ke hbe hb ht vf tv hga weq hbe hb ht vf wv
      ax-17 hbe hb ht hal hb ht hb vy hal vx tb hal vx tv kc tal hbe vy ta kl
      kc tan kbr kl hbe hb ht vf tv tex kt hal wex hal hb vx tb hal vx tv kc
      tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc
      tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy
      ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl hbe hb ht vf wv hbe hb ht
      hbe hb ht hb ht vy tex hbe hb ht vf tv hbe wex hbe hb ht vf wv ax-17 hbe
      hb ht hal hb vy vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hbe hb ht
      vf tv kt hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb
      hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe
      hb vy ta axrep.1 wl wc wov hbe hb ht vf wv hbe hb ht hb hb hb vy tb hal
      vx tv kc hbe hb ht vf tv tal hbe vy ta kl kc tan kt wan hal hb tb hal vx
      tv axrep.2 hal vx wv wc hbe hb ht vf wv hbe hb ht hb tal hbe vy ta kl hbe
      wal hbe hb vy ta axrep.1 wl wc hbe hb ht hb hb hb ht ht vy tan hbe hb ht
      vf tv wan hbe hb ht vf wv ax-17 hbe hb ht hb vy tb hal vx tv kc hbe hb ht
      vf tv hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht vf wv ax-17 hbe
      hb ht hbe hb ht hb vy hbe vy ta kl hbe hb ht vf tv tal kt hbe wal hbe hb
      vy ta axrep.1 wl hbe hb ht vf wv hbe hb ht hbe hb ht hb ht vy tal hbe hb
      ht vf tv hbe wal hbe hb ht vf wv ax-17 hbe hb ht hbe hb vy ta hbe hb ht
      vf tv kt axrep.1 hbe hb ht vf wv wtru hbl1 hbc hbov hbl hbc hbe hb ht hal
      hb ht hb vy hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hbe hb
      ht vf tv tex kt hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan
      kbr hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx
      tv axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy
      ta axrep.1 wl wc wov wl hbe hb ht vf wv hbe hb ht hbe hb ht hb ht vy tex
      hbe hb ht vf tv hbe wex hbe hb ht vf wv ax-17 hbe hb ht hal hb vy vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr hbe hb ht vf tv kt hb hb hb tb
      hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal
      vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc
      wov hbe hb ht vf wv hbe hb ht hb hb hb vy tb hal vx tv kc hbe hb ht vf tv
      tal hbe vy ta kl kc tan kt wan hal hb tb hal vx tv axrep.2 hal vx wv wc
      hbe hb ht vf wv hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta
      axrep.1 wl wc hbe hb ht hb hb hb ht ht vy tan hbe hb ht vf tv wan hbe hb
      ht vf wv ax-17 hbe hb ht hb vy tb hal vx tv kc hbe hb ht vf tv hal hb tb
      hal vx tv axrep.2 hal vx wv wc hbe hb ht vf wv ax-17 hbe hb ht hbe hb ht
      hb vy hbe vy ta kl hbe hb ht vf tv tal kt hbe wal hbe hb vy ta axrep.1 wl
      hbe hb ht vf wv hbe hb ht hbe hb ht hb ht vy tal hbe hb ht vf tv hbe wal
      hbe hb ht vf wv ax-17 hbe hb ht hbe hb vy ta hbe hb ht vf tv kt axrep.1
      hbe hb ht vf wv wtru hbl1 hbc hbov hbl hbc hbov hbl hbc hbe hb ht hbe hb
      vy vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc hbe hb
      ht vf tv kt hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc
      tan kbr kl hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr
      hb hb hb tb hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv
      axrep.2 hal vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta
      axrep.1 wl wc wov wl wc hbe hb ht vf wv hbe hb ht hal hb ht hb vy hal vx
      tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl hbe hb ht vf tv tex kt hal
      wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal
      vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx
      wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc
      wov wl hbe hb ht vf wv hbe hb ht hbe hb ht hb ht vy tex hbe hb ht vf tv
      hbe wex hbe hb ht vf wv ax-17 hbe hb ht hal hb vy vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr hbe hb ht vf tv kt hb hb hb tb hal vx tv kc tal
      hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb
      ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov hbe hb ht
      vf wv hbe hb ht hb hb hb vy tb hal vx tv kc hbe hb ht vf tv tal hbe vy ta
      kl kc tan kt wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht vf wv
      hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc hbe hb
      ht hb hb hb ht ht vy tan hbe hb ht vf tv wan hbe hb ht vf wv ax-17 hbe hb
      ht hb vy tb hal vx tv kc hbe hb ht vf tv hal hb tb hal vx tv axrep.2 hal
      vx wv wc hbe hb ht vf wv ax-17 hbe hb ht hbe hb ht hb vy hbe vy ta kl hbe
      hb ht vf tv tal kt hbe wal hbe hb vy ta axrep.1 wl hbe hb ht vf wv hbe hb
      ht hbe hb ht hb ht vy tal hbe hb ht vf tv hbe wal hbe hb ht vf wv ax-17
      hbe hb ht hbe hb vy ta hbe hb ht vf tv kt axrep.1 hbe hb ht vf wv wtru
      hbl1 hbc hbov hbl hbc hbl clf a1i mpbir hbe hb ht hbe vz tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc kl hbe hb ht vy tal hbe vz
      hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl
      kc tan kbr kl kc ke kbr kl kc kl hbe hb ht hb vy tal hbe vz hbe hb ht vy
      tv hbe vz tv kc tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      kc ke kbr kl kc hbe hb ht hb tal hbe vz hbe hb ht vy tv hbe vz tv kc tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc ke kbr kl hbe
      wal hbe hb vz hbe hb ht vy tv hbe vz tv kc tex hal vx tb hal vx tv kc tal
      hbe vy ta kl kc tan kbr kl kc ke kbr hb hbe hb ht vy tv hbe vz tv kc tex
      hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc hbe hb hbe hb ht
      vy tv hbe vz tv hbe hb ht vy wv hbe vz wv wc hal hb ht hb tex hal vx tb
      hal vx tv kc tal hbe vy ta kl kc tan kbr kl hal wex hal hb vx tb hal vx
      tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb hal vx tv kc tal hbe vy ta
      kl kc tan wan hal hb tb hal vx tv axrep.2 hal vx wv wc hbe hb ht hb tal
      hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc wov wl wc weqi wl wc wl
      hbe hb vz tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl kc
      hal hb ht hb tex hal vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr kl
      hal wex hal hb vx tb hal vx tv kc tal hbe vy ta kl kc tan kbr hb hb hb tb
      hal vx tv kc tal hbe vy ta kl kc tan wan hal hb tb hal vx tv axrep.2 hal
      vx wv wc hbe hb ht hb tal hbe vy ta kl hbe wal hbe hb vy ta axrep.1 wl wc
      wov wl wc wl ax4e syl wtru adantl ex $.
  $}

  ${
    $d x y $.  $d y A $.  $d p y z al $.
    axpow.1 $e |- A : ( al -> bool ) $.
    $( Axiom of Power Sets.  An axiom of Zermelo-Fraenkel set theory.
       (Contributed by Mario Carneiro, 10-Oct-2014.) $)
    axpow $p |- T. |=
      ( ? \ y : ( ( al -> bool ) -> bool ) . ( ! \ z : ( al -> bool ) .
        [ ( ! \ x : al .
            [ ( z : ( al -> bool ) x : al ) ==> ( A x : al ) ] ) ==>
          ( y : ( ( al -> bool ) -> bool ) z : ( al -> bool ) ) ] ) ) $=
      kt tal hal hb ht vz tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv
      kc tim kbr kl kc kt tim kbr kl kc tex hal hb ht hb ht vy tal hal hb ht vz
      tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr kl kc hal
      hb ht hb ht vy tv hal hb ht vz tv kc tim kbr kl kc kl kc hal hb ht vz tal
      hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr kl kc kt tim
      kbr kt kt tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr
      kl kc kt kt tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim
      kbr kl kc wtru hal hb ht hb tal hal vx hal hb ht vz tv hal vx tv kc ta
      hal vx tv kc tim kbr kl hal wal hal hb vx hal hb ht vz tv hal vx tv kc ta
      hal vx tv kc tim kbr hb hb hb hal hb ht vz tv hal vx tv kc ta hal vx tv
      kc tim wim hal hb hal hb ht vz tv hal vx tv hal hb ht vz wv hal vx wv wc
      hal hb ta hal vx tv axpow.1 hal vx wv wc wov wl wc simpl ex alrimiv hal
      hb ht hb ht vy tal hal hb ht vz tal hal vx hal hb ht vz tv hal vx tv kc
      ta hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc
      tim kbr kl kc hal hb ht vp kt kl tal hal hb ht vz tal hal vx hal hb ht vz
      tv hal vx tv kc ta hal vx tv kc tim kbr kl kc kt tim kbr kl kc hal hb ht
      hb ht hb tal hal hb ht vz tal hal vx hal hb ht vz tv hal vx tv kc ta hal
      vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc tim kbr
      kl hal hb ht wal hal hb ht hb vz tal hal vx hal hb ht vz tv hal vx tv kc
      ta hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc
      tim kbr hb hb hb tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc
      tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc tim wim hal hb ht
      hb tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr kl hal
      wal hal hb vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr hb hb
      hb hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim wim hal hb hal hb ht
      vz tv hal vx tv hal hb ht vz wv hal vx wv wc hal hb ta hal vx tv axpow.1
      hal vx wv wc wov wl wc hal hb ht hb hal hb ht hb ht vy tv hal hb ht vz tv
      hal hb ht hb ht vy wv hal hb ht vz wv wc wov wl wc hal hb ht hb vp kt
      wtru wl hal hb ht hb ht hb hal hb ht vz tal hal vx hal hb ht vz tv hal vx
      tv kc ta hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv
      kc tim kbr kl hal hb ht vz tal hal vx hal hb ht vz tv hal vx tv kc ta hal
      vx tv kc tim kbr kl kc kt tim kbr kl tal hal hb ht hb ht vy tv hal hb ht
      vp kt kl ke kbr hal hb ht wal hal hb ht hb vz tal hal vx hal hb ht vz tv
      hal vx tv kc ta hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb
      ht vz tv kc tim kbr hb hb hb tal hal vx hal hb ht vz tv hal vx tv kc ta
      hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc tim
      wim hal hb ht hb tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc
      tim kbr kl hal wal hal hb vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc
      tim kbr hb hb hb hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim wim hal
      hb hal hb ht vz tv hal vx tv hal hb ht vz wv hal vx wv wc hal hb ta hal
      vx tv axpow.1 hal vx wv wc wov wl wc hal hb ht hb hal hb ht hb ht vy tv
      hal hb ht vz tv hal hb ht hb ht vy wv hal hb ht vz wv wc wov wl hal hb ht
      hb vz tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim kbr kl
      kc hal hb ht hb ht vy tv hal hb ht vz tv kc tim kbr tal hal vx hal hb ht
      vz tv hal vx tv kc ta hal vx tv kc tim kbr kl kc kt tim kbr hal hb ht hb
      ht vy tv hal hb ht vp kt kl ke kbr hb hb hb tal hal vx hal hb ht vz tv
      hal vx tv kc ta hal vx tv kc tim kbr kl kc hal hb ht hb ht vy tv hal hb
      ht vz tv kc tim wim hal hb ht hb tal hal vx hal hb ht vz tv hal vx tv kc
      ta hal vx tv kc tim kbr kl hal wal hal hb vx hal hb ht vz tv hal vx tv kc
      ta hal vx tv kc tim kbr hb hb hb hal hb ht vz tv hal vx tv kc ta hal vx
      tv kc tim wim hal hb hal hb ht vz tv hal vx tv hal hb ht vz wv hal vx wv
      wc hal hb ta hal vx tv axpow.1 hal vx wv wc wov wl wc hal hb ht hb hal hb
      ht hb ht vy tv hal hb ht vz tv hal hb ht hb ht vy wv hal hb ht vz wv wc
      wov hb hb hb tal hal vx hal hb ht vz tv hal vx tv kc ta hal vx tv kc tim
      kbr kl kc hal hb ht hb ht vy tv hal hb ht vz tv kc tim hal hb ht hb ht vy
      tv hal hb ht vp kt kl ke kbr kt wim hal hb ht hb tal hal vx hal hb ht vz
      tv hal vx tv kc ta hal vx tv kc tim kbr kl hal wal hal hb vx hal hb ht vz
      tv hal vx tv kc ta hal vx tv kc tim kbr hb hb hb hal hb ht vz tv hal vx
      tv kc ta hal vx tv kc tim wim hal hb hal hb ht vz tv hal vx tv hal hb ht
      vz wv hal vx wv wc hal hb ta hal vx tv axpow.1 hal vx wv wc wov wl wc hal
      hb ht hb hal hb ht hb ht vy tv hal hb ht vz tv hal hb ht hb ht vy wv hal
      hb ht vz wv wc hb hal hb ht hb ht vy tv hal hb ht vz tv kc hal hb ht vp
      kt kl hal hb ht vz tv kc kt hal hb ht hb ht vy tv hal hb ht vp kt kl ke
      kbr hal hb ht hb hal hb ht hb ht vy tv hal hb ht vz tv hal hb ht hb ht vy
      wv hal hb ht vz wv wc hal hb ht hb hal hb ht vz tv hal hb ht hb ht vy tv
      hal hb ht hb ht vy tv hal hb ht vp kt kl ke kbr hal hb ht vp kt kl hal hb
      ht hb ht vy wv hal hb ht vz wv hal hb ht hb ht vy tv hal hb ht vp kt kl
      ke kbr hal hb ht hb ht hal hb ht hb ht vy tv hal hb ht vp kt kl hal hb ht
      hb ht vy wv hal hb ht hb vp kt wtru wl weqi id ceq1 hal hb ht vp kt kl
      hal hb ht vz tv kc kt ke kbr hal hb ht hb ht vy tv hal hb ht vp kt kl ke
      kbr hal hb ht hb ht hal hb ht hb ht vy tv hal hb ht vp kt kl hal hb ht hb
      ht vy wv hal hb ht hb vp kt wtru wl weqi hal hb ht hb vp kt kt hal hb ht
      vz tv wtru hal hb ht vz wv hb kt hal hb ht vp tv hal hb ht vz tv ke kbr
      hal hb ht hal hb ht vp tv hal hb ht vz tv hal hb ht vp wv hal hb ht vz wv
      weqi wtru eqid cl a1i eqtri oveq2 leq ceq2 cla4ev syl $.
  $}

  ${
    $d x y $.  $d p y z $.  $d y A $.  $d y z al $.  $d p y z al $.
    axun.1 $e |- A : ( ( al -> bool ) -> bool ) $.
    $( Axiom of Union.  An axiom of Zermelo-Fraenkel set theory.  (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    axun $p |- T. |=
      ( ? \ y : ( al -> bool ) . ( ! \ z : al . [ ( ? \ x : ( al -> bool ) .
        [ ( x : ( al -> bool ) z : al ) /\ ( A x : ( al -> bool ) ) ] ) ==>
          ( y : ( al -> bool ) z : al ) ] ) ) $=
      kt tal hal vz tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht
      vx tv kc tan kbr kl kc kt tim kbr kl kc tex hal hb ht vy tal hal vz tex
      hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr
      kl kc hal hb ht vy tv hal vz tv kc tim kbr kl kc kl kc hal vz tex hal hb
      ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc kt
      tim kbr kt kt tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht
      vx tv kc tan kbr kl kc kt kt tex hal hb ht vx hal hb ht vx tv hal vz tv
      kc ta hal hb ht vx tv kc tan kbr kl kc kct kt tex hal hb ht vx hal hb ht
      vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc wtru hal hb ht hb
      ht hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc
      tan kbr kl hal hb ht wex hal hb ht hb vx hal hb ht vx tv hal vz tv kc ta
      hal hb ht vx tv kc tan kbr hb hb hb hal hb ht vx tv hal vz tv kc ta hal
      hb ht vx tv kc tan wan hal hb hal hb ht vx tv hal vz tv hal hb ht vx wv
      hal vz wv wc hal hb ht hb ta hal hb ht vx tv axun.1 hal hb ht vx wv wc
      wov wl wc wct trud ex alrimiv hal hb ht vy tal hal vz tex hal hb ht vx
      hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb
      ht vy tv hal vz tv kc tim kbr kl kc hal vp kt kl tal hal vz tex hal hb ht
      vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc kt
      tim kbr kl kc hal hb ht hb tal hal vz tex hal hb ht vx hal hb ht vx tv
      hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz
      tv kc tim kbr kl hal wal hal hb vz tex hal hb ht vx hal hb ht vx tv hal
      vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz tv kc
      tim kbr hb hb hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb
      ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz tv kc tim wim hal hb ht
      hb ht hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv
      kc tan kbr kl hal hb ht wex hal hb ht hb vx hal hb ht vx tv hal vz tv kc
      ta hal hb ht vx tv kc tan kbr hb hb hb hal hb ht vx tv hal vz tv kc ta
      hal hb ht vx tv kc tan wan hal hb hal hb ht vx tv hal vz tv hal hb ht vx
      wv hal vz wv wc hal hb ht hb ta hal hb ht vx tv axun.1 hal hb ht vx wv wc
      wov wl wc hal hb hal hb ht vy tv hal vz tv hal hb ht vy wv hal vz wv wc
      wov wl wc hal hb vp kt wtru wl hal hb ht hb hal vz tex hal hb ht vx hal
      hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb ht vy
      tv hal vz tv kc tim kbr kl hal vz tex hal hb ht vx hal hb ht vx tv hal vz
      tv kc ta hal hb ht vx tv kc tan kbr kl kc kt tim kbr kl tal hal hb ht vy
      tv hal vp kt kl ke kbr hal wal hal hb vz tex hal hb ht vx hal hb ht vx tv
      hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz
      tv kc tim kbr hb hb hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta
      hal hb ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz tv kc tim wim hal
      hb ht hb ht hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht
      vx tv kc tan kbr kl hal hb ht wex hal hb ht hb vx hal hb ht vx tv hal vz
      tv kc ta hal hb ht vx tv kc tan kbr hb hb hb hal hb ht vx tv hal vz tv kc
      ta hal hb ht vx tv kc tan wan hal hb hal hb ht vx tv hal vz tv hal hb ht
      vx wv hal vz wv wc hal hb ht hb ta hal hb ht vx tv axun.1 hal hb ht vx wv
      wc wov wl wc hal hb hal hb ht vy tv hal vz tv hal hb ht vy wv hal vz wv
      wc wov wl hal hb vz tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal
      hb ht vx tv kc tan kbr kl kc hal hb ht vy tv hal vz tv kc tim kbr tex hal
      hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc
      kt tim kbr hal hb ht vy tv hal vp kt kl ke kbr hb hb hb tex hal hb ht vx
      hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb
      ht vy tv hal vz tv kc tim wim hal hb ht hb ht hb tex hal hb ht vx hal hb
      ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl hal hb ht wex hal
      hb ht hb vx hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr hb
      hb hb hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan wan hal hb
      hal hb ht vx tv hal vz tv hal hb ht vx wv hal vz wv wc hal hb ht hb ta
      hal hb ht vx tv axun.1 hal hb ht vx wv wc wov wl wc hal hb hal hb ht vy
      tv hal vz tv hal hb ht vy wv hal vz wv wc wov hb hb hb tex hal hb ht vx
      hal hb ht vx tv hal vz tv kc ta hal hb ht vx tv kc tan kbr kl kc hal hb
      ht vy tv hal vz tv kc tim hal hb ht vy tv hal vp kt kl ke kbr kt wim hal
      hb ht hb ht hb tex hal hb ht vx hal hb ht vx tv hal vz tv kc ta hal hb ht
      vx tv kc tan kbr kl hal hb ht wex hal hb ht hb vx hal hb ht vx tv hal vz
      tv kc ta hal hb ht vx tv kc tan kbr hb hb hb hal hb ht vx tv hal vz tv kc
      ta hal hb ht vx tv kc tan wan hal hb hal hb ht vx tv hal vz tv hal hb ht
      vx wv hal vz wv wc hal hb ht hb ta hal hb ht vx tv axun.1 hal hb ht vx wv
      wc wov wl wc hal hb hal hb ht vy tv hal vz tv hal hb ht vy wv hal vz wv
      wc hb hal hb ht vy tv hal vz tv kc hal vp kt kl hal vz tv kc kt hal hb ht
      vy tv hal vp kt kl ke kbr hal hb hal hb ht vy tv hal vz tv hal hb ht vy
      wv hal vz wv wc hal hb hal vz tv hal hb ht vy tv hal hb ht vy tv hal vp
      kt kl ke kbr hal vp kt kl hal hb ht vy wv hal vz wv hal hb ht vy tv hal
      vp kt kl ke kbr hal hb ht hal hb ht vy tv hal vp kt kl hal hb ht vy wv
      hal hb vp kt wtru wl weqi id ceq1 hal hb vp kt hal vz tv hal hb ht vy tv
      hal vp kt kl ke kbr wtru hal vz wv hal hb ht hal hb ht vy tv hal vp kt kl
      hal hb ht vy wv hal hb vp kt wtru wl weqi a17i eqtri oveq2 leq ceq2
      cla4ev syl $.
  $}

  $( ax-reg, ax-inf, and ax-ac are "true" in the broad strokes in HOL, but
     the set.mm versions of these axioms are not well-typed and so cannot be
     expressed. $)

$( $t

/* The '$ t' (no space between '$' and 't') token indicates the beginning
    of the typesetting definition section, embedded in a Metamath
    comment.  There may only be one per source file, and the typesetting
    section ends with the end of the Metamath comment.  The typesetting
    section uses C-style comment delimiters.  Todo:  Allow multiple
    typesetting comments */

/* These are the LaTeX and HTML definitions in the order the tokens are
    introduced in $c or $v statements.  See HELP TEX or HELP HTML in the
    Metamath program. */

/******* Web page format settings *******/

/* Page title, home page link */
htmltitle "Higher-Order Logic Explorer";
htmlhome '<A HREF="mmhol.html"><FONT SIZE=-2 FACE=sans-serif>' +
    '<IMG SRC="hol.gif" BORDER=0 ALT=' +
    '"Home" HEIGHT=32 WIDTH=32 ALIGN=MIDDLE>' +
    'Home</FONT></A>';
/* Optional file where bibliographic references are kept */
/* If specified, e.g. "mmset.html", Metamath will hyperlink all strings of the
   form "[rrr]" (where "rrr" has no whitespace) to "mmset.html#rrr" */
/* A warning will be given if the file "mmset.html" with the bibliographical
   references is not present.  It is read in order to check correctness of
   the references. */
htmlbibliography "mmhol.html";

/* Variable color key at the bottom of each proof table */
htmlvarcolor '<FONT COLOR="#0000FF">type</FONT> '
    + '<FONT COLOR="#FF0000">var</FONT> '
    + '<FONT COLOR="#CC33CC">term</FONT>';

/* GIF and Unicode HTML directories - these are used for the GIF version to
   crosslink to the Unicode version and vice-versa */
htmldir "../holgif/";
althtmldir "../holuni/";


/******* Symbol definitions *******/

htmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  althtmldef "wff" as '<FONT COLOR="#808080">wff </FONT>';
  latexdef "wff" as "\mathrm{wff}";
htmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  althtmldef "var" as '<FONT COLOR="#808080">var </FONT>';
  latexdef "var" as "\mathrm{var}";
htmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  althtmldef "type" as '<FONT COLOR="#808080">type </FONT>';
  latexdef "type" as "\mathrm{type}";
htmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  althtmldef "term" as '<FONT COLOR="#808080">term </FONT>';
  latexdef "term" as "\mathrm{term}";
htmldef "|-" as
    "<IMG SRC='_vdash.gif' WIDTH=10 HEIGHT=19 ALT='|-' ALIGN=TOP> ";
  althtmldef "|-" as
    '<FONT COLOR="#808080" FACE=sans-serif>&#8866; </FONT>'; /* &vdash; */
    /* Without sans-serif, way too big in FF3 */
  latexdef "|-" as "\vdash";
htmldef ":" as "<IMG SRC='colon.gif' WIDTH=4 HEIGHT=19 ALT=':' ALIGN=TOP>";
  althtmldef ":" as ':';
  latexdef ":" as ":";
htmldef "." as " ";
  althtmldef "." as ' ';
  latexdef "." as "\,";
htmldef "|=" as
    " <IMG SRC='models.gif' WIDTH=12 HEIGHT=19 ALT='|=' ALIGN=TOP> ";
  althtmldef "|=" as "&#8871;"; latexdef "|=" as "\models";
htmldef "bool" as
    "<IMG SRC='hexstar.gif' WIDTH=11 HEIGHT=19 ALT='*' ALIGN=TOP>";
  althtmldef "bool" as '&lowast;';
  latexdef "bool" as "\ast";
htmldef "ind" as
    "<IMG SRC='iota.gif' WIDTH=6 HEIGHT=19 ALT='iota' ALIGN=TOP>";
  althtmldef "ind" as '<FONT SIZE="+1">&iota;</FONT>';
  latexdef "ind" as "\iota";
htmldef "->" as
    " <IMG SRC='to.gif' WIDTH=15 HEIGHT=19 ALT='-&gt;' ALIGN=TOP> ";
  althtmldef "->" as ' &rarr; ';
  latexdef "->" as "\rightarrow";
htmldef "(" as "<IMG SRC='lp.gif' WIDTH=5 HEIGHT=19 ALT='(' ALIGN=TOP>";
  althtmldef "(" as "(";
  latexdef "(" as "(";
htmldef ")" as "<IMG SRC='rp.gif' WIDTH=5 HEIGHT=19 ALT=')' ALIGN=TOP>";
  althtmldef ")" as ")";
  latexdef ")" as ")";
htmldef "," as "<IMG SRC='comma.gif' WIDTH=4 HEIGHT=19 ALT=',' ALIGN=TOP> ";
  althtmldef "," as ', ';
  latexdef "," as ",";
htmldef "\" as "<IMG SRC='lambda.gif' WIDTH=9 HEIGHT=19 ALT='\' ALIGN=TOP>";
  althtmldef "\" as '<I>&lambda;</I>';
  latexdef "\" as "\lambda";
htmldef "=" as " <IMG SRC='eq.gif' WIDTH=12 HEIGHT=19 ALT='=' ALIGN=TOP> ";
  althtmldef "=" as ' = '; /* &equals; */
  latexdef "=" as "=";
htmldef "T." as "<IMG SRC='top.gif' WIDTH=11 HEIGHT=19 ALT='T.' ALIGN=TOP>";
  althtmldef "T." as '&#x22A4;';
  latexdef "T." as "\top";
htmldef "[" as "<IMG SRC='lbrack.gif' WIDTH=5 HEIGHT=19 ALT='[' ALIGN=TOP>";
  althtmldef "[" as '['; /* &lsqb; */
  latexdef "[" as "[";
htmldef "]" as "<IMG SRC='rbrack.gif' WIDTH=5 HEIGHT=19 ALT=']' ALIGN=TOP>";
  althtmldef "]" as ']'; /* &rsqb; */
  latexdef "]" as "]";
htmldef "al" as
    "<IMG SRC='_alpha.gif' WIDTH=12 HEIGHT=19 ALT='al' ALIGN=TOP>";
  althtmldef "al" as '<FONT COLOR="#0000FF"><I>&alpha;</I></FONT>';
  latexdef "al" as "\alpha";
htmldef "be" as
    "<IMG SRC='_beta.gif' WIDTH=11 HEIGHT=19 ALT='be' ALIGN=TOP>";
  althtmldef "be" as '<FONT COLOR="#0000FF"><I>&beta;</I></FONT>';
  latexdef "be" as "\beta";
htmldef "ga" as
    "<IMG SRC='_gamma.gif' WIDTH=11 HEIGHT=19 ALT='ga' ALIGN=TOP>";
  althtmldef "ga" as '<FONT COLOR="#0000FF"><I>&gamma;</I></FONT>';
  latexdef "ga" as "\gamma";
htmldef "de" as
    "<IMG SRC='_delta.gif' WIDTH=9 HEIGHT=19 ALT='de' ALIGN=TOP>";
  althtmldef "de" as '<FONT COLOR="#0000FF"><I>&delta;</I></FONT>';
  latexdef "de" as "\delta";
htmldef "x" as "<IMG SRC='_x.gif' WIDTH=10 HEIGHT=19 ALT='x' ALIGN=TOP>";
  althtmldef "x" as '<I><FONT COLOR="#FF0000">x</FONT></I>';
  latexdef "x" as "x";
htmldef "y" as "<IMG SRC='_y.gif' WIDTH=9 HEIGHT=19 ALT='y' ALIGN=TOP>";
  althtmldef "y" as '<I><FONT COLOR="#FF0000">y</FONT></I>';
  latexdef "y" as "y";
htmldef "z" as "<IMG SRC='_z.gif' WIDTH=9 HEIGHT=19 ALT='z' ALIGN=TOP>";
  althtmldef "z" as '<I><FONT COLOR="#FF0000">z</FONT></I>';
  latexdef "z" as "z";
htmldef "f" as "<IMG SRC='_f.gif' WIDTH=9 HEIGHT=19 ALT='f' ALIGN=TOP>";
  althtmldef "f" as '<I><FONT COLOR="#FF0000">f</FONT></I>';
  latexdef "f" as "f";
htmldef "g" as "<IMG SRC='_g.gif' WIDTH=9 HEIGHT=19 ALT='g' ALIGN=TOP>";
  althtmldef "g" as '<I><FONT COLOR="#FF0000">g</FONT></I>';
  latexdef "g" as "g";
htmldef "p" as "<IMG SRC='_p.gif' WIDTH=10 HEIGHT=19 ALT='p' ALIGN=TOP>";
  althtmldef "p" as '<I><FONT COLOR="#FF0000">p</FONT></I>';
  latexdef "p" as "p";
htmldef "q" as "<IMG SRC='_q.gif' WIDTH=8 HEIGHT=19 ALT='q' ALIGN=TOP>";
  althtmldef "q" as '<I><FONT COLOR="#FF0000">q</FONT></I>';
  latexdef "q" as "q";
htmldef "A" as "<IMG SRC='_ca.gif' WIDTH=11 HEIGHT=19 ALT='A' ALIGN=TOP>";
  althtmldef "A" as '<I><FONT COLOR="#CC33CC">A</FONT></I>';
  latexdef "A" as "A";
htmldef "B" as "<IMG SRC='_cb.gif' WIDTH=12 HEIGHT=19 ALT='B' ALIGN=TOP>";
  althtmldef "B" as '<I><FONT COLOR="#CC33CC">B</FONT></I>';
  latexdef "B" as "B";
htmldef "C" as "<IMG SRC='_cc.gif' WIDTH=12 HEIGHT=19 ALT='C' ALIGN=TOP>";
  althtmldef "C" as '<I><FONT COLOR="#CC33CC">C</FONT></I>';
  latexdef "C" as "C";
htmldef "F" as "<IMG SRC='_cf.gif' WIDTH=13 HEIGHT=19 ALT='F' ALIGN=TOP>";
  althtmldef "F" as '<I><FONT COLOR="#CC33CC">F</FONT></I>';
  latexdef "F" as "F";
htmldef "R" as "<IMG SRC='_cr.gif' WIDTH=12 HEIGHT=19 ALT='R' ALIGN=TOP>";
  althtmldef "R" as '<I><FONT COLOR="#CC33CC">R</FONT></I>';
  latexdef "R" as "R";
htmldef "S" as "<IMG SRC='_cs.gif' WIDTH=11 HEIGHT=19 ALT='S' ALIGN=TOP>";
  althtmldef "S" as '<I><FONT COLOR="#CC33CC">S</FONT></I>';
  latexdef "S" as "S";
htmldef "T" as "<IMG SRC='_ct.gif' WIDTH=12 HEIGHT=19 ALT='T' ALIGN=TOP>";
  althtmldef "T" as '<I><FONT COLOR="#CC33CC">T</FONT></I>';
  latexdef "T" as "T";
htmldef "F." as "<IMG SRC='perp.gif' WIDTH=11 HEIGHT=19 ALT='F.' ALIGN=TOP>";
  althtmldef "F." as '&perp;';
  latexdef "F." as "\bot";
htmldef "/\" as
    " <IMG SRC='wedge.gif' WIDTH=11 HEIGHT=19 ALT='/\' ALIGN=TOP> ";
  althtmldef "/\" as ' <FONT FACE=sans-serif>&and;</FONT> ';
    /* althtmldef "/\" as ' <FONT FACE=sans-serif>&#8896;</FONT> '; */
    /* was &and; which is circle in Mozilla on WinXP Pro (but not Home) */
    /* Changed back 6-Mar-2012 NM */
  latexdef "/\" as "\wedge";
htmldef "~" as "<IMG SRC='lnot.gif' WIDTH=10 HEIGHT=19 ALT='~' ALIGN=TOP> ";
  althtmldef "~" as '&not; ';
  latexdef "~" as "\lnot";
htmldef "==>" as
    " <IMG SRC='bigto.gif' WIDTH=15 HEIGHT=19 ALT='==&gt;' ALIGN=TOP> ";
  althtmldef "==>" as ' &rArr; ';
  latexdef "==>" as "\Rightarrow";
htmldef "!" as "<IMG SRC='forall.gif' WIDTH=10 HEIGHT=19 ALT='A.' ALIGN=TOP>";
  althtmldef "!" as '<FONT FACE=sans-serif>&forall;</FONT>'; /* &#8704; */
  latexdef "!" as "\forall";
htmldef "?" as "<IMG SRC='exists.gif' WIDTH=9 HEIGHT=19 ALT='E.' ALIGN=TOP>";
  althtmldef "?" as '<FONT FACE=sans-serif>&exist;</FONT>'; /* &#8707; */
    /* Without sans-serif, bad in Opera and way too big in FF3 */
  latexdef "?" as "\exists";
htmldef "\/" as " <IMG SRC='vee.gif' WIDTH=11 HEIGHT=19 ALT='\/' ALIGN=TOP> ";
  althtmldef "\/" as ' <FONT FACE=sans-serif> &or;</FONT> ' ;
    /* althtmldef "\/" as ' <FONT FACE=sans-serif>&#8897;</FONT> ' ; */
    /* was &or; - changed to match font of &and; replacement */
    /* Changed back 6-Mar-2012 NM */
  latexdef "\/" as "\vee";
htmldef "?!" as "<IMG SRC='_e1.gif' WIDTH=12 HEIGHT=19 ALT='E!' ALIGN=TOP>";
  althtmldef "?!" as '<FONT FACE=sans-serif>&exist;!</FONT>';
  latexdef "?!" as "\exists{!}";
htmldef "typedef" as "typedef ";
  althtmldef "typedef" as 'typedef ';
  latexdef "typedef" as "\text{ typedef }";
htmldef "1-1" as "1-1 ";
  althtmldef "1-1" as '1-1 ';
  latexdef "1-1" as "\mathrm{1-1}";
htmldef "onto" as "onto ";
  althtmldef "onto" as 'onto ';
  latexdef "onto" as "\mathrm{onto}";
htmldef "@" as
    "<IMG SRC='varepsilon.gif' WIDTH=8 HEIGHT=19 ALT='@' ALIGN=TOP>";
  althtmldef "@" as '&epsilon;';
  latexdef "@" as "\varepsilon";

/* End of typesetting definition section */
$)

$( 456789012345 (79-character line to adjust text window width) 567890123456 $)
