  
(** %\chapter{%#<H0>#Finite automata%}%#</H0># *)

(* Proofs *)
 Section Automata.
(*Load FinSets.*)
Load Finitesets.

Require Import List.
Fixpoint foldr (A B :Type)(f:A ->B->  B) (z:B) (xs: list A) :=

      match xs with
        | nil => z
        | cons x xs' => f x (foldr f z xs')
      end.
Definition orbool  (xs: list (bool)) : bool := foldr (orb ) false xs.
Definition anyl (A:Type)(p:A->bool)(xs:list A):bool := orbool( map p xs).
Definition elem (n:nat)(x:Fin n)(xs:list (Fin n)) :bool := anyl ( eqf x) xs.

Definition In_bool (n:nat) (x:Fin n)(xs: list (Fin n)) : bool := elem x xs.
Set Implicit Arguments.


(*Definition Alphabet := nat.*)
(*Variable Sigma : Alphabet. *) 

(** * Introduction 

  In finite automata theory, the basic element that we need to use in order  to reason about the behaviour of an automaton is the _word_ . 

  By definition, we call  a word to be a list of _symbols_. 

    
  - A symbol is an element of an alphabet( usually denoted as $\Sigma $ ).

  - A set of words is defined to be called a _language_ .

  In our implementation , a language is represented as a function that takes a word 

  and decides whether it is a member of the set (type [Prop]).

      *)
Definition Word(x:Alphabet) := list (Fin x).

Definition Language (a:Alphabet):= Word a -> Prop.



Inductive Starl(c:Alphabet)(x:Language c) : Language c := 
  | nil0: (Starl x) nil
  | cons0 : forall (a: Word c)(b:Word c),Starl x a /\ x b -> Starl x (app a b).


(** An empty word is defined as the [nil] list constructor *)



Definition eps (a:Alphabet):Word a:=nil.



(**  * Deterministic finite automata 

  As in "Automata and theory of computation"(J.Hopcroft), a deterministic finite automaton
  
 (DFA) is defined a 5-uple (Q,$\Sigma $ , $\sigma $, ${q}_{0}$, F)

  - A finite set of states Q (here denoted by [states])

  - A set of symbols ([Fin a])

  - A transition function $\sigma $ : Q * $\Sigma $ -> Q , denoted by [delta]

  - An initial state ${q}_{0}$

  - A set of final states F .

*)

Record dfa (n:nat) (a:Alphabet) :Type:= DFA {  
  states :=  Fin n; (*finite sets*) 
  symbol := Fin a;  
  delta : Fin n ->Fin a  -> Fin n; 
  q0 : Fin n ; (*only 1 initial state*)
  final :Fin n -> bool (*multiple states*)
}.
Check dfa.

(** * Language of a finite deterministic automaton *)


(*Definition is_accepting (n:nat)(a:Alphabet)(d:dfa n a)(q: states d)  := In q (final d).*)

(** Below, we have the extended transition function for a DFA , [deltah] : *)


Fixpoint deltah (n:nat)(a:Alphabet)(d: dfa n a)(q: Fin n) (w: Word a) : (Fin n):=
  match w with
     | nil => q
     | h :: t => (deltah d (delta  d q h ) t) 
  end.
Lemma deltah_prop:
  forall (a:Alphabet)(n:nat)(q:Fin n) (d:dfa n a) (xs ys :Word a),
   deltah d (q) (xs++ ys) = deltah d (deltah d (q) xs) ys.

induction xs.
simpl in *.
reflexivity.
simpl in *.

intros.
simpl in *.
(*induction ys.
simpl in *.
assert (xs++nil = xs).
intuition.
rewrite H.
reflexivity.
simpl in *.
intuition. *)
admit.
Qed.
Lemma deltah_property :
    forall (a:Alphabet)(n:nat) (d:dfa n a)(q:Fin n)(xs ys zs :Word a) ,
   deltah d (q) (xs ++ ys ++ zs) =
    deltah d(deltah d (deltah d (q) xs) ys ) zs.
induction xs.
simpl.
induction ys.
simpl in *.
reflexivity.
simpl in *.
apply deltah_prop.


simpl in *.
intros.
assert (xs ++ ys ++ zs = (xs ++ ys)++ zs).
auto with *.
admit.



(*simpl in *.
induction xs.


induction zs.
simpl in *.
intuition.
assert (ys ++ nil = ys).
intuition.
 (*very well known property*)
rewrite H.
reflexivity.
simpl in *. *)

Qed.


Notation " x ^ y " := (exps x y).

Definition dfa_lang1 (n:nat)(a:Alphabet)(d: dfa n a) :Language a := 
  fun w:Word a => final  d (deltah  d(q0 d ) w)=true.


(** The actual definition of the language of a DFA *)

Definition dfa_lang (n:nat)(a:Alphabet)(d: dfa n a) :Language a := 
  fun w:Word a =>  match final  d (deltah  d(q0 d ) w) with
               | true => True
               | false => False end.
(*
Definition dfa_lang (n:nat)(a:Alphabet)(d: dfa n a) :Language a := 
  fun w:Word a => final  d (deltah  d(q0 d ) w) =true. *)
  

Check dfa_lang.
Check tt.

Fixpoint dfa_seq (a:Alphabet)(n:nat)(d:dfa n a)(x:Fin n)(w:Word a) : list(Fin n) :=
    match w with 
   | nil => nil
   | a :: es => delta d x a :: dfa_seq d ( delta d x a) es
    end.

(** Empty automaton : a (initial )state with no final states*)


Definition dfa_void(q:Fin 1)(a:Alphabet) : dfa 1 a := 
          DFA (fun x:Fin 1 => fun b:Fin a => q ) q (fun x:Fin 1 => false).

Print dfa_void.

(** The empty automaton will not accept any word *)

Definition empty_lang (a:Alphabet):Language a:= fun w:Word a=>False.

Definition isNil (a:Alphabet) (w:Word a): Prop :=
    match w with  |nil => True
                  | _  => False
                              end. 

Definition eps_lang (a:Alphabet) :Language a := 

             fun w:Word a=> w=nil.

              (*fun w:Word a => match w with  |nil => True
                                            | _  => False
                              end. *)

Definition eps_lang1 (a:Alphabet) :Language a := 
        fun w:Word a => w =nil.
Check tt.
Print tt.

Lemma dfa_void_correct1 : forall (a:Alphabet)(q:Fin 1) (w:Word a), 

    final (dfa_void q a)( deltah (dfa_void q a) q w )= false.
intros.
simpl in *.
reflexivity.
Qed.


Lemma dfa_void_correct: forall (a:Alphabet)(q:Fin 1) (w:Word a),
     dfa_lang (dfa_void q a) w -> empty_lang w.
intros.
unfold dfa_lang in H.
unfold empty_lang.
simpl in H.

auto with *.
Qed.

(*The automaton that will take the epsilon language *)

Print option.
Check (S (S 0)).
Definition dfa_epsilon (q:Fin 1)(a:Alphabet) : dfa (1) a := 
   DFA( fun _:Fin 1 => fun _:Fin a=> q) q   (fun x:Fin 1 => false (*if eqf x q then true else false*) (*eqf x q*)).
Check dfa_lang.

Check dfa_epsilon.
(*
Lemma dfa_eps_aux: forall (a:Alphabet)(q:Fin 1)(k:Fin 2)(w:Word a), final (dfa_epsilon q a)( deltah (dfa_epsilon q a) q w )= false.

intros.
simpl in *. *)
Lemma dfa_eps_correct: 
      forall (a:Alphabet) (q:Fin 1)(w:Word a) , dfa_lang (dfa_epsilon q a) w ->w = nil.
 
intros.
simpl in *.
induction w.
reflexivity.
simpl in *.
unfold dfa_lang in *.
simpl in *.
assert (dfa_lang(dfa_epsilon q a)(a0::w) -> False).
intros.
simpl in *.

unfold dfa_lang in *.
simpl in *.
case_eq (eqf (deltah (dfa_epsilon q a) q w) q).
intros.
destruct H0.
destruct H0.
destruct H0.
destruct H.
(*
rewrite H1 in H.
simpl in *.
rewrite H1 in IHw.
rewrite H1 in H0.
destruct H0.
destruct H. *)
Qed.

Definition dfa_compl (a:Alphabet)(n:nat)(d:dfa n a) : dfa n a :=

   DFA( delta d) (q0 d) (fun q : Fin n=> 

    negb (final d q)). 

Inductive empty :Set := .
Inductive singleton :Set := emptyx : singleton. 
Print emptyx.


Print dfa.
(*Definition dfa_char (a:Alphabet)(ch : Fin a) : dfa 2 a:=
     DFA( fun x : Fin 2 => fun c:Fin a => eqf 

Definition nfa_var(a:Alphabet)(cc:Fin a)  :=
    NFA( fun it :Fin 2 => fun aa :Fin a =>  allexp1 (fun final:Fin 2=>if negb (eqf it final)&& eqf cc aa then true  else  false ))
      (fun x : Fin 2 => existsf1 (fun y: Fin 2 => eqf x y) )
    (fun x:Fin 2 => existsf1 ( fun y :Fin 2 => eqf x y)). *)

(** Remove states that are unreachable !!! *)


Definition reachable_immediate (a:Alphabet) (n:nat) (d: dfa n a)(x y :Fin n)  :=

  exists c:Fin a,   (delta d x c) = y.


Definition reachablea (a:Alphabet)(n:nat) (d:dfa n a) (y:Fin n) :=

   exists w:Word a , deltah d ( q0 d)w = y.
Check reachablea.
Fixpoint dfa_seq1 (a:Alphabet)(n:nat)(d:dfa n a)(x:Fin n)(w:Word a) : list(Fin n) :=
    match w with 
   | nil => nil
   | a :: es => delta d x a :: dfa_seq1 d ( delta d x a) es
    end.

Definition reachable1 (n:nat)(a:Alphabet)(d:dfa n a) := 

          fun x y : Fin n =>  exists c, delta d x c = y .
Definition is_decidable (A:Set) (P:A->Prop) := forall a, {P a} + {~(P a)}.

Variable list_comprehension: forall A : Set, list A -> forall P : A -> Prop, is_decidable  P -> list A.
Implicit Arguments list_comprehension [A].

Notation "[ e | b <- l , Hp ]" := (map (fun b:_=> e) (list_comprehension l (fun b:_=>_ ) Hp))  (at level 1).
Hypothesis  Zlt_decide:forall (a:nat) , is_decidable  (fun x=>x<a).
Definition elt_lt_x l pivot:= [ y | y <- l , (Zlt_decide pivot) ].

Hypothesis Zlt_decide1 :forall (a:Alphabet)(n:nat)(d:dfa n a), is_decidable( fun y=>reachable1 d (q0 d) y).
Definition reachable'(n:nat)(a:Alphabet)(d:dfa n a)(qs:list (Fin n)): list(Fin n):= [q | q <- qs ,Zlt_decide1 d ].



Fixpoint removedups (n:nat) (xs : list (Fin n)) : list (Fin n):= match xs with
   | nil => nil
   | x::xs => if In_bool x xs then removedups xs else x::removedups xs
 end.
  
Definition reachable (n:nat)(a:Alphabet)(d:dfa n a)(qs:list(Fin n)) :list (Fin n):= removedups(reachable' d qs).
 Hypothesis Zlt_decideilist :forall (n:nat)(xs : list(Fin n)), is_decidable( fun x=>In x xs).
Definition inters_list (n:nat)(ass bs:list(Fin n)) : list(Fin n):=let ns := [ a | a <- ass, Zlt_decideilist bs] in [ b | b <- bs, Zlt_decideilist ns].
Check length.

Definition connected_states(n:nat)(a:Alphabet)(d:dfa n a) (qs:list (Fin n)) : list(Fin n) := inters_list qs (reachable d qs).  
Definition nr_connected_states(n:nat)(a:Alphabet)(d:dfa n a)(qs:list(Fin n)) :nat := length(connected_states d qs).

Hypothesis Zlt_decidecon : forall (n:nat)(a:Alphabet)(c:Fin a)(d:dfa n a)(x:Fin n) , is_decidable(fun y=>  y=((delta d) x c)).

Axiom Zlt_decideelem : forall (n:nat)(a:Alphabet)(d:dfa n a)(qs:list(Fin n)) (x:Fin n)(c:Fin a), is_decidable(fun y => In x (connected_states d qs) /\ In ((delta d) x c) (connected_states d qs  ) /\ (delta d) x c =y).

Check Zlt_decideelem.
Definition helpcon (a:Alphabet)(n:nat)(d:dfa n a)(qs:list(Fin n))(x:Fin n)(c:Fin a) : list(Fin n):=
      [y | y <- qs , Zlt_decideelem d  qs x c ].

 Definition head_list (n:nat)(dum: Fin n)(l:list (Fin n)): Fin n:=
    match l with
      | nil => dum
      | x :: xs =>  x
    end.
Check (fun n:nat => fun x y:Fin n => head_list y (x::nil)).
Definition dfa_connected (a:Alphabet)(n:nat)(dum:Fin n)(d:dfa n a)(qs:list(Fin n)):=
   DFA(fun x:Fin n  => fun c:Fin a => 
              
 head_list dum (helpcon d qs x c)   
           )
    

    (q0 d) (fun x => (elem x (connected_states d qs))).

Check dfa_connected.
Definition A_c (a:Alphabet)(n:nat)(du :Fin n)(d:dfa n a)(qs:list(Fin n)):= dfa_connected   du d qs.
Definition last (A:Type)(x:A)(xs:list A) :A := 
     match xs with 
   | nil => x
   | p:: xs' => last xs' x
   end.
 Definition f_M (a:Alphabet)(n:nat)(du:Fin n)(d:dfa n a)(qs:list (Fin n)):= fun w:Word a => last (q0 (A_c du d qs)) (dfa_seq (A_c du d qs)(q0 (A_c du d qs))  w).

Definition isconnected (a:Alphabet)(n:nat) (d:dfa n a) :=

    forall (x:Fin n), exists w:Word a, deltah d (q0 d) w = x.  

(** * Nondeterministic finite automaton 

   A _nondeterministic finite automaton_ (NFA) A is defined as a 5-uple Q,$\Sigma $ , $\sigma $, S, F), 
   where :

   - [Q] represent a finite set of initial states ( [nstates])

   - A set of symbols $\Sigma $ ([Fin a])

   - A transition function $\sigma $ : Q * $\Sigma $ -> $P (Q)$ ([ndelta])

   - A set of initial states [S] , denoted by [ninitial]

   - A set of final states [F], denoted by [nfinal].

   
*)


Record nfa (n:nat)(a:Alphabet) := NFA {
   
   nstates :=Fin n; 
   nsymbol := Fin a; 
   ndelta : Fin n-> Fin a  ->Fin (2^n); 
   ninitial : Fin n -> bool (* multiple states*);
   nfinal : Fin n -> bool
 }.
Check nfa.

(** We want to generate the union of 2 sets, taking into account the isomorphism [(Fin n -> bool) <-> Fin (2^n)], proven in the library of

    finite sets. *)


Definition unionf (n:nat) (sets : (Fin n -> bool) -> bool) (x:Fin n) : bool := 
  existsf1 (fun q : Fin (2^n) => sets( allexp2 q) && allexp2 q x).

Definition prepare (n:nat)(a:Alphabet) (nr:nfa n a)(states : Fin (2^n)) (x:Fin a)  : (Fin n -> bool)  :=
   fun s : Fin n  => existsf1 (fun st : Fin n => allexp2 (states) (st) &&  allexp2(ndelta  nr st x) s). 


(** The extended transition function for an NFA  [ndeltah]: *)

Fixpoint ndeltah (n : nat) (a:Alphabet) (nr: nfa n a) (qs : (Fin (2^ n))) (w:Word a) :(Fin (2^n)) :=
       match w with 
     | nil    =>  qs
     | h :: t =>  (ndeltah nr (allexp1 (prepare nr qs h)) t)   
       end.
(*Definition nfa_lang (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => (existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q)))=true. 
*)
Definition nfa_lang (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => match (existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q))) with
                   | true => True
                  | false => False
                   end .
Definition nfa_lang1 (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a =>(existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q))) = true.
Definition nfa_lang01 (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => exists  q :Fin n ,  allexp2(ndeltah nr (allexp1 (ninitial nr) ) w) q && (nfinal  nr q)=true. 

(** * The subset construction *)

(*Convert a dfa to an nfa: *)

Definition dfa2nfa (n:nat) (a:Alphabet) (d:dfa n a): nfa n a :=
    NFA(fun k : Fin n => fun a : Fin a => 
    
     (allexp1 ( fun x:Fin n => eqf x (delta d k a) ))) (fun x:Fin n => eqf x (q0 d)) (final d).




(* union of ndelta *)

  
Definition nfa2dfa (n:nat) (a:Alphabet) (nr: nfa n a) : dfa (2^n) a :=

 DFA (fun k:Fin (2^n)=> fun a : Fin a => allexp1 (prepare nr k a)) (allexp1 (ninitial nr )) 
    (fun k:Fin (2^n)=>existsf1(fun q:Fin n=> (allexp2 k q ) && nfinal nr  q)).

Definition nfa_void (a:Alphabet) : nfa 1 a :=
  NFA(fun x:Fin 1 => fun a:Fin a=> allexp1 (fun y:Fin 1 => false)) 
      (fun x:Fin 1 =>existsf1 (fun y:Fin 1 => eqf x y))
       (fun x:Fin 1 =>existsf1 (fun y:Fin 1 => false)).

Lemma nfa_void_lang :  forall (a:Alphabet)(w:Word a),
     nfa_lang (nfa_void a) w -> empty_lang w.
intros.
unfold empty_lang.
unfold nfa_lang in H.
simpl in H.
auto with *.

Qed.
Print eps.
(*
Definition chec (a:Alphabet) (p :Fin a) :=

 if (p::nil)=eps a then true else false.*)

Definition nfa_eps(a:Alphabet):nfa 1 a :=

  NFA(fun x:Fin 1 => fun a0:Fin a => allexp1 (fun y:Fin 1 => false))
   (fun x:Fin 1 => true ) (fun x:Fin 1 => true).


Print nfa_eps.

Print option.

Lemma nfa_eps_lang1 : forall (a:Alphabet)(w:Word a) ,
     eps_lang w -> nfa_lang (nfa_eps a) w.
intros.
unfold eps_lang in H.
unfold nfa_lang.
simpl.
split.
Qed.
Lemma nfa_eps_lang :forall (a:Alphabet) (w:Word a) ,
   nfa_lang1 (nfa_eps a) w -> eps_lang w.
intros.
unfold eps_lang.

unfold nfa_lang1 in H.
unfold nfa_eps in *.
simpl in *.
induction w.
reflexivity.
destruct H.
rewrite IHw.
admit.
Qed.

(*
Definition nfa_var (a:Alphabet) :=

   NFA (fun xs : Fin 2 => fun c:Fin a => 

     allexp1 (fun ys : Fin 2 => eqf xs ys =false) )

     (fun xs :Fin 2 =>   *)

Definition nfa_var(a:Alphabet)(cc:Fin a)  :=
    NFA( fun x :Fin 2 => fun b :Fin a =>  allexp1 (fun final:Fin 2=>if negb (eqf x final)then if eqf cc b then true  else  false else false))
      (fun x : Fin 2 => existsf1 (fun y: Fin 2 => false) )
    (fun x:Fin 2 => existsf1 ( fun y :Fin 2 => false)). (* ???*)
(*
Definition nfa_var(a:Alphabet)(cc:Fin a)  :=
    NFA( fun x :Fin 2 => fun b :Fin a =>  allexp1 (fun final:Fin 2=>if negb (eqf x final)then if eqf cc b then true  else  false else false ))
      (fun x : Fin 2 => existsf1 (fun y: Fin 2 => if eqf x y then false else true) )
    (fun x:Fin 2 => existsf1 ( fun y :Fin 2 => if eqf x y then true else false)).

*)

(*
Definition nfa_var(a:Alphabet)(cc:Fin a)  :=
    NFA( fun it :Fin 2 => fun aa :Fin a =>  allexp1 (fun final:Fin 2=>if negb (eqf it final)&& eqf cc aa then true  else  false ))
      (fun x : Fin 2 => existsf1 (fun y: Fin 2 => eqf x y) )
    (fun x:Fin 2 => existsf1 ( fun y :Fin 2 => eqf x y)). *)

Print nfa_var.
(*
Definition nfa_var1(a:Alphabet)(x:Fin a) : nfa 2 a:=

   NFA (fun xs :Fin 2 => fun c :Fin a => allexp1(existsf1(fun y:Fin 2 =>
           end))) tt tt. *)
Print option.

Definition single_lang (a:Alphabet):Language a:=
  fun w => 

match w with 
        | a::nil => True
        | _ => False
     end.
Print single_lang.

Definition single_lang1 (a:Alphabet)(x:Fin a) :Language a :=
  fun w : Word a => match w with 
    
     | p :: nil => if eqf p x then True else False
     | _ => False
    end. 
Lemma nfa_var_lang : forall (a:Alphabet)(w:Word a)(cc:Fin a) , 
    nfa_lang (nfa_var  cc) w  -> w =cc::nil.
intros.
unfold nfa_lang in H.
(*intuition.
(*We want to prove that in an nfa with the epsilon language does not accept a word
different from <nil>  useful in the theorem of correctness nfa_eps_lang *)
rewrite H0 in H.
assert(False). *)
unfold nfa_var in *.
simpl in *.
destruct H.
Qed.
Print nfa_var.

Print sum.
Print prod.



Definition condition1 (a:Alphabet)(p q :nat) (c:Fin a) (n1:nfa p a)(n2:nfa q a) (xd : Fin (p+q)) : bool :=

         match (addfin1 p q xd) with 
        | inl x => existsf1 (fun tx:Fin(2^p) => eqf tx (ndelta n1 x c))

        | inr y => existsf1 (fun ty :Fin (2^q) => eqf ty (ndelta n2 y c))

       end.
       

Definition nfa_disj (a:Alphabet)(p q :nat) (n1:nfa p a)(n2:nfa q a) : nfa(p+q) a :=

    NFA( fun xs : Fin (p+q) => fun c:Fin a => 

    allexp1 (fun xss :Fin (p+q) => eqf xs xss &&  condition1 c n1 n2 xss))
   
    (fun xs :Fin (p+q) =>

       match (addfin1 p q xs) with 
    
          | inl x => ninitial n1 x

          | inr y => ninitial n2 y

     end)


    (fun xs :Fin (p+q)  => 

       match (addfin1 p q xs) with 
    
          | inl x => nfinal n1 x

          | inr y => nfinal n2 y

     end) .

Definition lang_conc(a:Alphabet)(l1:Language a)(l2:Language a):Language a:=
    fun w:Word a=> exists w1:Word a, exists w2:Word a,  w1 ++ w2=w /\ l1 w1 /\ l2 w2.

Definition lang_union(a:Alphabet) (l1:Language a )(l2:Language a):Language a:=
    fun w:Word a=>  l1 w \/ l2 w.
Print nfa_lang.

Print ndeltah.
Check (fun p q : nat =>fun s : Fin p=>fun ss : Fin q => fun x: Fin p+ Fin q =>inl s ).

(*
Fixpoint nfa_accept (n:nat)(a:Alphabet)(nr : nfa n a) (x:Fin n)(w :Word a) :=
match w with
  | nil =>nfinal nr x
  | a::w => nfa_accept nr (ndelta nr x a) w
end.
Lemma nfa_disj_correct': forall (p q: nat) (a:Alphabet)(n1 : nfa p a) (n2: nfa q a)(w:Word a) (xs:Fin (p+q)),

   nfinal (  nfa_disj n1 n2 ) (ndeltah (  nfa_disj n1 n2 )(allexp1 (fun xs' => eqf xs xs') )w).
  [ predU dfa_accept A1 x.1 & dfa_accept A2 x.2 ]
    =i dfa_accept dfa_disj x. *)
Lemma nfa_disj_lang : forall (a:Alphabet) (p q:nat) (n1: nfa p a) (n2: nfa q a) (w:Word a), 

        nfa_lang1( nfa_disj n1 n2 ) w -> lang_union (nfa_lang1 n1  ) (nfa_lang1 n2 ) w.
intros.
unfold lang_union.
unfold nfa_lang1 in *.
simpl in H.

simpl in *.
(** This goal states: there exists a state q1 of type Fin p that satisfies the fact

   that it is a final state in the nfa n1. The analogue statement is for the nfa n2*)
simpl in *.
(**Any automaton is made of final states*)
left.


set( f1 := allexp2  (ndeltah n1 (allexp1  (ninitial n1)) w)).

set (f := fun t :Fin p => nfinal n1 t).
set( PP:= fun qx :Fin (p+q) => match addfin1 p q qx with 
  | inl x => nfinal n1 x
 
  | inr y => nfinal n2 y end).
apply exss in H.
destruct H.
assert (Fin p + Fin q).
apply addfin1.
exact x.
assert(exists t:Fin p , f t = true).
unfold f.
intuition.
exists a0.
admit.

simpl in *.

Check (inr (addfin1 p q x)).

admit.

admit.
 (*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!111
left.
admit. *)
Qed.

Lemma nfa_disj_lang1 : forall (a:Alphabet) (p q:nat) (n1: nfa p a) (n2: nfa q a) (w:Word a), 

       lang_union (nfa_lang1 n1  ) (nfa_lang1 n2 ) w -> nfa_lang1 ( nfa_disj n1 n2 ) w.
intros.
unfold lang_union in *.
unfold nfa_lang1 in *.
destruct H.
simpl in *.
set( PP:= fun qx :Fin (p+q) => match addfin1 p q qx with 
  | inl x => nfinal n1 x
 
  | inr y => nfinal n2 y end).

set (pp:= fun q :Fin p => nfinal n1 q).
admit.

simpl in *.
admit.

(*
intros.
unfold lang_union.
unfold nfa_lang.
simpl in *.
unfold nfa_lang in H.
simpl in *.
left.
case_eq( existsf1(fun q1:Fin p => nfinal n1 q1)).
intro.
split.
intro.


left.*)

Qed.

Eval compute in existsf1( fun y: Fin 3=>(existsf1 (fun x:Fin 2 => true&& false))).

Print sum.

(*Inductive empty :Set := .*)
(**For a set with a single element, we consider an element x defined itself on  the singleton.

*)
(*Inductive singleton :Set := emptyx : singleton.  *)

Check (inr  emptyx).
Check existsf1(fun (t:Fin 2)=> existsf1 (fun o : Fin 2 => eqf t o )).

Print nfa_disj.

Check ( fun (c:Fin 2) => fun (d:Fin 3)=> inr (Fin 3) c).


Definition nfa_conc(a:Alphabet)(p q:nat) (n1:nfa p a) (n2:nfa q a) : nfa( p+q) a:=

    NFA( fun xs:(Fin (p+q)) => fun c:Fin a=>
  ( allexp1( fun xss:Fin (p+q) => eqf xss xs && (  existsf1 (fun x:Fin p=> existsf1(fun y:Fin q =>

          (*
      match addfin1 x , addfin1 y with 

      | inl x , inl y =>  existsf1 (fun t:Fin (2^p) => (eqf(ndelta n1 x c) t))

      | inl x, inr y =>  (nfinal n1 x) && ndelta (n2) *)
  
      
         match (addfin1 p q xs) with
       | inl  x => existsf1 (fun t:Fin (2^p) => (eqf(ndelta n1 x c) t)) ||

                          existsf1 (fun q'': Fin q => existsf1 (fun q' :Fin p => 

                     existsf1 (fun tx:Fin (2^p)=>

                        (nfinal n1 q') && (ninitial n2 q'') && (allexp2 (ndelta n1 x c) q'))))

       | inr  y => existsf1( fun tr: Fin (2^q) => (eqf(ndelta n2 y c) tr))

        end ))))))
      (fun xs :Fin (p+q) =>
          existsf1(fun x:Fin p => existsf1(fun y:Fin q =>

           match  (addfin1 p q xs) with
         | inl x =>  ninitial n1 x

         | inr y => nfinal n2 y && existsf1( fun t: Fin p => ninitial n1 t && nfinal n1 t)

         end)))

     (fun xs :Fin (p+q) =>
        existsf1 (fun x:Fin p=> existsf1(fun y:Fin q =>
           match  (addfin1 p q xs) with

         | inl x =>  false

         | inr y => nfinal n2 y 
        end ))).
         
    
Print nfa_conc.


Lemma nfa_conc1 : forall (a:Alphabet) (p q:nat)
        (n1 :nfa p a) (n2 : nfa q a)  (w:Word a) ,

   nfa_lang1 (nfa_conc n1 n2) w -> lang_conc (nfa_lang1 n1) (nfa_lang1 n2) w.

intros.
unfold lang_conc in *.
unfold nfa_lang1 in *.
simpl in *.
admit . (*??*)
Qed.
Definition nfa_star (a:Alphabet) (p:nat) (n1:nfa p a) : nfa (p+1) a := 

    NFA( fun xs:Fin (p+1) => fun c:Fin a=>  

    allexp1 (fun xss:Fin(p+1) => eqf xs xss && existsf1( fun _:Fin p =>

        match (addfin1 p 1 xs) with

     | inl x => existsf1 (fun tx:Fin (2^p) => eqf tx (ndelta n1 x c)) ||

                existsf1 (fun q' :Fin p => existsf1 (fun tx:Fin (p) =>

                           (ninitial n1 q') &&  (allexp2  (ndelta n1 x c) tx )&& (nfinal n1 tx)))

     | inr y => false

   end )))
    
    (fun xs:Fin (p+1) => 

        match (addfin1 p 1 xs) with

    | inl x => ninitial n1 x
   
    | inr y => true
 

       end)

     (fun xs:Fin (p+1) => 

        match (addfin1 p 1 xs) with

    | inl x => nfinal n1 x
   
    | inr y => true
 

       end) .

    


     

     
Lemma nfa_eps_lang12 :  forall (a:Alphabet)(w:Word a),
     nfa_lang1 (nfa_eps a) w -> eps_lang1 w.

intros.
unfold nfa_lang1 in H.

unfold eps_lang1.

simpl in *.
destruct w.
split.
inversion H.
induction w.
simpl.

simpl. (*
rewrite IHw.

simpl in H.
simpl in IHw.
inversion H.
simpl in IHw.
unfold isNil in IHw.*)
(*induction w.
split.
simpl in H.
simpl in IHw.
apply IHw in H.
simpl in H. *)

admit.
admit.
Qed. 
Check negb.
Print negb.
Check inl.


Lemma dfa2nfa_correct2 : forall (n:nat)(a:Alphabet)(w:Word a)(d:dfa n a), 
              dfa_lang d w-> nfa_lang (dfa2nfa d)w.
intros.
unfold dfa_lang in H.
unfold nfa_lang.
simpl.
      

case_eq (existsf1 (fun q:Fin n => final d q)).
intros.
split.
intro.
assert( final d (deltah d (q0 d) w)=false).
admit.

(*must prove that if there is no state that is final, then 
also the initial state cannot be final, taken as a particular case of the problem *)

rewrite H1 in H.
destruct H.
(*reflexivity.*)
Qed.

Lemma dfa2nfa_correct1 : forall (n:nat)(a:Alphabet)(w:Word a)(d:dfa n a), 
               nfa_lang (dfa2nfa d)w-> dfa_lang d w .
(*intros.
unfold nfa_lang1 in *.
unfold dfa_lang1 in *.
simpl in *.*)




intros.
unfold nfa_lang in H.
simpl in H.
unfold dfa_lang.
simpl.
simpl in H.
case_eq (existsf1 (fun q:Fin n => final d q)).
intro.
simpl.
simpl in *.
rewrite H0 in H.

case_eq (final d (deltah d (q0 d) w)).
split.
intro.
admit.
intro.

rewrite H0 in H.
destruct H.
Qed.


Theorem nfa2dfa_correct1 :forall (n:nat)(a:Alphabet)(w:Word a) (nr:nfa n a),
       dfa_lang (nfa2dfa nr) w -> nfa_lang nr w.
Proof.
intros.
unfold dfa_lang in H.
unfold nfa_lang.
simpl in H.
simpl.
exact H.
Qed.

Theorem nfa2dfa_correct2: forall (n:nat)(a:Alphabet)(w:Word a) (nr:nfa n a),
       nfa_lang nr w -> dfa_lang (nfa2dfa nr) w.
Proof.
intros.
unfold dfa_lang.
unfold nfa_lang in H.
simpl.
simpl in H.
assumption.
Qed.

(*Lemma for the equivalence of extended transition functions of a DFA and an NFA*)
Lemma eqref: forall (n:nat) (p :Fin n)  , equalsf p p =true.
intros.
induction n.
simpl.

assert (False).
apply fin0empty.
exact p.
destruct H.

unfold equalsf.
unfold equalsf in IHn.
simpl.
admit. (*prove inductive step *)
Qed.
Lemma ext_delta_coincide: forall (n:nat)(a:Alphabet) (nr:nfa n a)(w:Word a) , 
    eqf (ndeltah nr  (allexp1(ninitial nr)) w)(deltah (nfa2dfa nr) (q0 (nfa2dfa nr)) w)=true.

intros.
unfold eqf.
simpl.
induction w.
simpl.
rewrite eqref.


reflexivity.

set(P:=deltah (nfa2dfa nr) (allexp1 (ninitial nr )) w).

assert(deltah (nfa2dfa nr) (allexp1 (ninitial nr)) (a0:: w) = 

      (deltah (nfa2dfa nr) (delta  (nfa2dfa nr) (allexp1 (ninitial nr)) a0 ) w)).
simpl. 
reflexivity.
simpl.
trivial.

Qed.
 






Set Implicit Arguments.
Require Import Logic.

Definition surj (X Y :Type)  (f :X-> Y) :=
 
   forall y:Y,  exists x:X, f(x) = y.
Print deltah.

Definition collapse_rel (a:Alphabet)(n:nat)(d:dfa n a )(x y : states d) :=


   forall w:Word a , final d(deltah d x w)=true <-> final d(deltah d y w) =true. 


Record Fin_Equiv (A:Set) := make_eq {
rel :> A->A->Prop;

 Eq_refl : forall x:A, rel x x;
 
 Eq_trans : forall (x y z :A), rel x y -> rel y z -> rel x z;
 Eq_sym  : forall (x y :A) , rel x y -> rel y x
 
} .


Record fin_eq_class (a:Alphabet)(n:nat) :=

 {
     fin_func :> Word a -> Fin n;
    
     fin_surj : surj  (fin_func)


 }.
Check False_ind.

(*
Definition is_decidable (A:Set) (P:A->Prop) := forall a, {P a} + {~(P a)}.

Variable list_comprehension: forall A : Set, list A -> forall P : A -> Prop, is_decidable  P -> list A.
Implicit Arguments list_comprehension [A].

Notation "[ e | b <- l , Hp ]" := (map (fun b:_=> e) (list_comprehension l (fun b:_=>_ ) Hp))  (at level 1).
Hypothesis  Zlt_decide:forall (a:nat) , is_decidable  (fun x=>x<a).
Definition elt_lt_x l pivot:= [ y | y <- l , (Zlt_decide pivot) ].
Lemma choose: forall (n:nat)(P:exists x:Fin n, )(y:Fin n), Fin n. *)

Lemma can_repr : forall(a:Alphabet)(n:nat)(f:fin_eq_class a n)(x:Word a)(e:exists y:Fin n , f x =y)  , Word a.
intros.
admit.
Qed.
(*Definition cr(a:Alphabet)(n:nat)(f:fin_eq_class a n)(x:Word a):Prop := choose(fin_surj f x). *)
(*Right congruence property *)
Definition rcongruence (a:Alphabet) (X:Type) (f : Word a-> X)


     :=  forall (x y  w:Word a), f x = f y -> f (x++ w) = f (y++ w).


Definition refines(a:Alphabet)(X:Type) (f: Word a -> X)(l:Language a) := forall (x y aa:Word a),

    f x = f y -> l x =l y.

(** We will split the Myhill_nerode theorem into several parts . Let us define 

    a record for a specific type of relation, that satisfies right_invariant property [congruence],
    
    and also has the property of equality of the mapping on the words [x] and [y],

    implying that they  *)

Record Myhill_rel (a:Alphabet)(n:nat)(L:Language a):=

   {
      myhill_func :> fin_eq_class a n;

     myhill_congruent : rcongruence myhill_func;
     myhill_belongs : refines (myhill_func ) L


    }.

Definition exP (n:nat)( P: Fin n -> bool):= existsf1(fun x :Fin n=>P x).

Check (fun a:Alphabet=> fun n:nat =>fun f:fin_eq_class  a n=> fin_surj f).
Print surj.

Variable A B :Type.
Definition funchoice := forall R: A->B->Prop, 
                         
                      (forall x:A, exists y:B, R x y)->

                  (exists f:A->B, forall x:A, R x (f x)).  


Definition choose(n:nat)(a:Alphabet) (P:fin_eq_class a n-> Prop):= exists x:fin_eq_class a n, P x.
Definition c_repr(n:nat)(a:Alphabet) := choose(fun f: fin_eq_class a n => surj f).
Check (fun (a:Alphabet)(n:nat) => fun f:fin_eq_class a n=> choose(fun c: fin_eq_class a n => surj c)).
(*
Check (fun (a:Alphabet)(n:nat) => fun f:fin_eq_class a n=> choose(fin_surj f)).
Definition xchoose (n:nat)(a:Alphabet)(P:fin_eq_class a n-> Prop) (p:existsf1(fun x:Fin n => P x)) :=
     
Definition canon_repr (a:Alphabet)(n:nat)( f: fin_eq_class a n) :=
*)

Definition suffix_congruence (a:Alphabet)(u v :Word a)(l:Language a):= 

  forall ( w :Word a) , l (u ++ w) = l(v++w).

Definition eq_suffix_cong (a:Alphabet) (X:Type) (f :Word a -> X) (l:Language a):=

    forall (u v :Word a) , f u = f v <-> suffix_congruence u v l.


Definition imply_suffix (a:Alphabet)(X:Type) (f:Word a -> X) (l:Language a):=
   forall (u v :Word a), f u =f v -> suffix_congruence u v l.

Record Nerode_rel (a:Alphabet)(n:nat) (L:Language a) :=
   {
      nerode_func :> fin_eq_class a n ; 

      nerode_equiv : eq_suffix_cong nerode_func L
    


   }.
(*
Lemma nerode1 : forall (a:Alphabet)(n:nat)(L:Language a)
 
        (f:Nerode_rel a n)(w:Word a),  *)

Record Nerode_rel_weak (a:Alphabet)(n:nat) (L:Language a) :=

   { nerode_func_weak :> fin_eq_class a n;
     

     nerode_equiv_weal:imply_suffix nerode_func_weak L

   }.


  Record nerode_weak_nerode (a:Alphabet)(n:nat)(L:Language a)(f: Nerode_rel a L):=
      NWK{ weak_nerode_imply := fun u v H => match nerode_equiv f u v with conj H0 H1 => H0 H end }.

Check nerode_weak_nerode.
  (*Coercion nerode_weak_nerode : Nerode_rel >-> Nerode_rel_weak.
   *) 
Check A_c.
Check last.

Check f_M.
Check Zlt_decideelem.
Check f_M.
Print f_M.
 Lemma f_M_surjective: forall (a:Alphabet)(n:nat) (du:Fin n)(d:dfa n a)(qs:list(Fin n))(w:Word a), surj (f_M du d  qs ).
intros.
unfold f_M.
unfold A_c.
unfold dfa_connected.
simpl in *.
intuition.
simpl.
unfold surj.
simpl in *.
intros.
simpl in *.

(* to complete *)

(** 1) Language L is accepted by a dfa
    2) we are able to construct a Myhill relation for L
    3) we can construct a weak nerode relation for L
    *)

(* 2 => 3 *)
Lemma myhill_to_wkner: forall (a:Alphabet)(n:nat)(l:Language a)(f: Myhill_rel n l),

       imply_suffix f l.
intros.
unfold imply_suffix.
induction f.
simpl in *.
intros.
unfold suffix_congruence.
unfold iff.
intros.

unfold refines in myhill_belongs0.
unfold rcongruence in myhill_congruent0.
apply (myhill_congruent0 u v w)in H.
apply myhill_belongs0 in H.
exact H.
exact w.
Qed. 

Lemma myhill_weak_ner : forall (a:Alphabet)(n:nat)(l:Language a) (f:Myhill_rel n l),
     Nerode_rel_weak  n l.
intros.
exact {|
        nerode_func_weak := f;
        nerode_equiv_weal := myhill_to_wkner  f 
      |}.
Qed.


Section Nerode_to_Dfa.



 Definition nerode_to_dfa(a:Alphabet)(n:nat) (L:Language a)(f:Nerode_rel a n L) :=
        DFA(fun x:Fin n => c:Fin a => f 
        dfa_s := f nil;
        dfa_fin := [pred x | cr f x \in L ];
        dfa_step := [fun x a => f (rcons (cr f x) a)]
      


End Nerode_to_Dfa.


(** Language L is accepted by a dfa -> we are able to construct a myhill relation for l *)

(** Let us construct a function which we later on we prove to be surjective. Our 

  final goal is to create a relation from the language accepted *)

Definition dfa_connected (a:Alphabet)(n:nat)(d:dfa n a) := isconnected d.


Definition func_dfa (a:Alphabet)(n:nat)(d:dfa n a ) := fun w:Word a =>
                deltah d(q0 d) w.

Print deltah.
Lemma deltah_is_surj : forall (a:Alphabet) (n:nat)(d:dfa n a), surj (deltah d (q0 d)).
intros.
unfold surj.
intro.

(*apply y in w.
exists w.
(*rewrite y.
exists (q0 d).*) *)
admit.
Qed.

(* We will define the equivalence relation by using the fact that the extended

   transition function is surjective.

   The extended function will describe an equivalence relation and it will have to be 


   able to have the properties of a right-invariant, as well as the property of 

   the fact that two words are equivalent, and one of them belong to the language [L],

  then they both belong to the same language .*)

Definition deltah_fin_eq_class (a:Alphabet)(n:nat)(d:dfa n a): fin_eq_class a n:=

   {| fin_func := deltah d (q0 d);

     fin_surj := deltah_is_surj d

   |}.

(* Now we show that the relation has the property of right-invariance (congruence) *)
Check deltah_prop.
Lemma right_congruent1 : forall (a:Alphabet)(n:nat)(d:dfa n a), 
                     congruence (deltah d (q0 d)).
intros.
unfold congruence.
intros.
assert (deltah d (q0 d) (x++w ) = deltah d (deltah d (q0 d) (x) ) w ).
apply deltah_prop.

assert (deltah d (q0 d) (y ++ w ) = deltah d (deltah d (q0 d) y ) w ).
apply deltah_prop.
rewrite H1.
rewrite <-H.
apply deltah_prop.
Qed.

(* Once we have proven that the extended transition function is right invariant, 
we will prove that it also have the following property : *)

Check dfa_lang.
Lemma belongs1 : forall (a:Alphabet) (n:nat) (d:dfa n a), 

       belongs (deltah d (q0 d) ) (dfa_lang d) .
intros.
unfold belongs.
intros.
unfold dfa_lang.
rewrite H.
reflexivity.
Qed.


Definition dfa_rel  (a:Alphabet)(n:nat) (d:dfa n a): Myhill_rel n (dfa_lang d):=
   {|  myhill_func := deltah_fin_eq_class d ;
       myhill_congruent := right_congruent1 d;

       myhill_belongs := belongs1 d
   |}.

Definition equal_language (a:Alphabet)(L1 L2:Language a) :=
   forall w:Word a , L1 w = L2 w.
Lemma lang_myh_equiv : forall (a:Alphabet)(n:nat)(l1 l2 :Language a),
 
       equal_language l1 l2 -> Myhill_rel n l1 -> Myhill_rel n l2.
intros.

unfold iff in H.
induction H0.
unfold equal_language in H.
unfold congruence in myhill_congruent0.
unfold belongs in myhill_belongs0.
assert(fin_eq_class a n).
exact myhill_func0.

(** We will consider to take the same function [myhill_func0] that we will use

   for the language [l2], and prove the relation of [myhill_belongs0] using the 

   property [l1 w = l2 w] *)
(*
assert (forall x y w :Word a, H0 x = H0 y ->
      H0 (x++w) = H0 (y++w)).
intros. *)

assert ( forall x y :Word a, Word a -> myhill_func0 x = myhill_func0 y ->
      l2 x = l2 y).
intros.
assert(l1 x = l1 y).

apply (myhill_belongs0 x y H1 H2).
assert(l1 x = l2 x).
apply H.
assert(l1 y = l2 y).
apply H.
assert (l2 x = l1 y).

rewrite H3 in H4.
symmetry.
exact H4.
rewrite <-H6 in H5.
assumption.

admit.

(* TO DO *)

Qed.


Print nil.

Print eps.
Check (fun (n:nat)(a:Alphabet)(l:Language a)(f:Nerode_rel n l) => f (eps a)).
Print dfa_connected.


(** Transform a nerode relation into a deterministic finite automaton *)
(*Definition choose_from (a:Alphabet)(n:nat)(f:Nerode_rel n a)(exP :exists x:Word a, f x)  := 

*)
(*We must use for equivalent classes the canonical form : every object under consideration
is equivalent to exactly one object in canonical form;  in other words, the canoninal forms of set [M]
represent the equivalence classes once and only once *)



Check (fun (a:Alphabet)(n:nat)(l:Language a)(f:Nerode_rel  n l)(x:Word a) => 
           can_repr f x ).

Definition ner_to_autom (a:Alphabet)(n:nat)(l:Language a)(f:Nerode_rel a n l) :=

   {| 
       delta :=  fun xs :Fin n => fun c: Fin a =>

         allexp1 (fun xss:Fin n => eqf xss xs && 

         exists t:Word a , (f t) = xs 

         existsf1(fun tt:Word a => can_repr(f t)) ;
       
      q0 := f (eps a);
   
      final := fun xs :Fin n => 

   |}.
existsf1(t:Word a=> eqf (f t) x && f (rc(can_repr f t))
Lemma autom_rel : forall (a:Alphabet)(n:nat) (d:dfa n a) , Myhill_rel n (dfa_lang d).
intros.
unfold dfa_lang.
Require Import List.


(* From automaton section - reachability *)

Lemma reachable0 : forall (a:Alphabet) (n:nat) (d:dfa n a),

         reachable d(q0 d).
intros.
unfold reachable.
exists nil.
simpl.
reflexivity.
Qed.

Lemma reachable_step : forall (a:Alphabet) (n:nat) (d:dfa n a)(x:Fin n)(c:Fin a) ,
         reachable d (x) -> reachable d (delta d x c).

intros.
unfold reachable in *.
destruct H.
induction x0.
simpl in *.

exists (c::nil).
simpl in *.
rewrite H.
reflexivity.

?
simpl in *.
simpl in H.
inversion H.
simpl in *.

exists (a0::x0 ++(c ::nil)).
simpl.
 
admit.
(* true *)
(* !!!*)

Qed.



(** Minimization : merge equivalence classes *)
Lemma myhill_suffix : forall (a:Alphabet) (L:Language a), 



Definition ff (a:Alphabet)(n:nat)(d:dfa n a):= fun w:Word a=> (q0 d).


End Myhill_nerode.
