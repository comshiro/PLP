Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).


(* Environment *)
Definition Env := string -> nat.
Definition env0 :=
  fun (x : string) => 0.
Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.



(* <AExp, Env> => <nat> *)

Reserved Notation "A =[ S ]=> V"  (at level 60).
Inductive aeval : AExp -> Env -> nat -> Type :=
| const : forall n sigma, (num n) =[ sigma ]=> n 
| lookup : forall x sigma, (var x) =[ sigma ]=> (sigma x)
| bs_add : forall a1 a2 sigma i1 i2 n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = i1 + i2 ->
  a1 +' a2 =[ sigma ]=> n
| bs_mul : forall a1 a2 sigma i1 i2 n,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 ->
  n = i1 * i2 -> 
  a1 *' a2 =[ sigma ]=> n 
where "A =[ S ]=> V" := (aeval A S V).


Example e1 : "x" +' 2 =[ update env0 "x" 10 ]=> 12.
Proof.
  apply bs_add with (i1 := 10) (i2 := 2).
  - apply lookup.
  - apply const.
  - simpl.
    reflexivity.
Qed.

Example e1' : "x" +' 2 =[ update env0 "x" 10 ]=> 12.
Proof.
  eapply bs_add.
  - apply lookup.
  - apply const.
  - simpl.
    reflexivity.
Qed.




(* boolean *)
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| blt : AExp -> AExp -> BExp.

Notation "B1 &&' B2" :=
  (band B1 B2) (left associativity,
      at level 65).
Notation "!' B" :=
  (bnot B) (at level 62).
Notation "A1 <' A2" :=
  (blt A1 A2)
    (at level 60).


Check Nat.ltb.
Reserved Notation "B -[ S ]-> B'"  (at level 80).
Inductive beval : BExp -> Env -> bool -> Type :=
| tt : forall sigma, btrue -[ sigma ]-> true 
| ff : forall sigma, bfalse -[ sigma ]-> false
| notTrue : forall b sigma,
  b -[ sigma ]-> true -> 
  bnot b -[ sigma ]-> false
| notFalse : forall b sigma,
  b -[ sigma ]-> false -> 
  !' b -[ sigma ]-> true
| andTrue : forall b1 b2 b sigma,
  b1 -[ sigma ]-> true ->
  b2 -[ sigma ]-> b ->
  b1 &&' b2 -[ sigma ]-> b 
| andFalse : forall b1 b2 sigma,
  b1 -[ sigma ]-> false ->
  b1 &&' b2 -[ sigma ]-> false
| blt1 : forall a1 a2 i1 i2 b sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 -> 
  b = Nat.ltb i1 i2 -> 
  a1 <' a2 -[ sigma ]-> b
where "B -[ S ]-> B'" := (beval B S B').


Definition env1 :=
  update
    (update
       (update env0 "i" 10)
       "j" 11)
    "n" 12.

Example e2 :
  "i" <' "j" +' 4 &&' btrue -[ env1 ]-> true.
Proof.
  apply andTrue.
  - eapply blt1.
    + apply lookup.
    + eapply bs_add.
      * apply lookup.
      * apply const.
      * simpl.
        reflexivity.
    + trivial.
  - apply tt.
Qed.

Create HintDb mydb.
Hint Constructors beval : mydb.
Hint Constructors aeval : mydb.
Hint Unfold Nat.ltb : mydb.
Hint Unfold env1 : mydb.

Example e2' :
  "i" <' "j" +' 4 &&' btrue -[ env1 ]-> true.
Proof.
  eauto with mydb.
Qed.


(* statements *)
Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assign X A)
                        (at level 90).
Notation "S1 ; S2" := (seq S1 S2)
                        (at level 98).


Reserved Notation "S ~[ E ]~> E'" (at level 99).
Inductive eval : Stmt -> Env -> Env -> Type :=
| b_assign : forall x a v sigma sigma',
  a =[ sigma ]=> v ->
  sigma' = update sigma x v -> 
  (x ::= a) ~[ sigma ]~> sigma'
| b_seq : forall s1 s2 sigma1 sigma2 sigma3,
  s1 ~[ sigma1 ]~> sigma2 ->
  s2 ~[ sigma2 ]~> sigma3 -> 
  (s1 ; s2) ~[ sigma1 ]~> sigma3
| while_t : forall b s sigma sigma',
  b -[ sigma ]-> true ->
  (s ; while b s) ~[ sigma ]~> sigma' ->
  (while b s) ~[ sigma ]~> sigma'
| while_f : forall b s sigma,
  b -[ sigma ]-> false ->
  (while b s) ~[ sigma ]~> sigma 
| ite_t : forall b sigma sigma' s1 s2,
  b -[ sigma ]-> true ->
  s1 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
| ite_f : forall b sigma sigma' s1 s2,
  b -[ sigma ]-> false ->
  s2 ~[ sigma ]~> sigma' ->
  (ite b s1 s2) ~[ sigma ]~> sigma'
where "S ~[ E ]~> E'" := (eval S E E').

Hint Constructors eval : mydb.
Hint Unfold env0 : mydb.

Example e3:
  (assign "n" 10) ~[ env0 ]~> update env0 "n" 10.
Proof.
  eauto with mydb.
Qed.



Check (assign "n" 10).
Check (assign "i" 0).
Check (assign "s" ("s" +' "i")).

Check "n" ::= 10.
Check "i" ::= 0.
Check "s" ::= "s" +' "i".

Check ite ("i" <' "n")
          ( "i" ::= "i" +' 1)
          ( "i" ::= "i" *' 1).

Check while ("i" <' "n")
  ("s" ::= "s" +' "i").

Check skip.
Check seq ("s" ::= "s" +' "i")
  ("i" ::= "i" +' 1).

Check
  "s" ::= "s" +' "i" ;
"i" ::= "i" +' 1.


Definition sum :=
"n" ::= 10 ;
"i" ::= 0 ;
"s" ::= 0 ;
while ("i" <' "n" +' 1) (
    "s" ::= "s" +' "i" ;
    "i" ::= "i" +' 1
  ).
