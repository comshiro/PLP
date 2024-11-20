Require Import String.
Open Scope string_scope.

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



Reserved Notation "A -[ S ]-> V"  (at level 60).
Inductive aeval_ss : AExp -> Env -> AExp
                     -> Type :=
| lookup : forall x sigma,
    (var x) -[ sigma ]-> (sigma x)
| ss_add1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 +' a2) -[ sigma ]-> a1' +' a2
| ss_add2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 +' a2) -[ sigma ]-> a1 +' a2'
| ss_add : forall (i1 i2 : nat) sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n 
| ss_mul1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 *' a2) -[ sigma ]-> a1' *' a2
| ss_mul2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 *' a2) -[ sigma ]-> a1 *' a2'
| ss_mul : forall (i1 i2 : nat) sigma,
  (i1 *' i2) -[ sigma ]-> i1 * i2 
where "A -[ S ]-> V" := (aeval_ss A S V).


Example e1 : "x" +' 2 -[ update env0 "x" 10 ]->
             10 +' 2.
Proof.
  apply ss_add1.
  apply lookup.
Qed.

Reserved Notation "A -< S >* V"  (at level 61).
Inductive a_clos : AExp -> Env -> AExp
                   -> Type :=
| a_refl : forall a sigma, a -< sigma >* a
| a_tran : forall a1 a2 a3 sigma,
  a1 -[ sigma ]-> a2 ->
  a2 -< sigma >* a3 -> 
  a1 -< sigma >* a3
where "A -< S >* V" := (a_clos A S V).

Example e1' : "x" +' 2
              -< update env0 "x" 10 >*
              12.
Proof.
  eapply a_tran.
  - apply e1.
  - eapply a_tran.
    + apply ss_add.
      reflexivity.
    + simpl.
      apply a_refl.
Qed.

Definition envXY :=
  update (update env0 "x" 10) "y" 11.

Example e2_xy :
  "x" +' "y" -< envXY >* 21.
Proof.
  eapply a_tran.
  - apply ss_add1.
    apply lookup.
  - unfold  envXY, update.
    simpl.
    eapply a_tran.
    + apply ss_add2.
      apply lookup.
    + eapply a_tran.
      apply ss_add.
      reflexivity.
      simpl.
      apply a_refl.
Qed.

Example e2_yx :
  "x" +' "y" -< envXY >* 21.
Proof.
  eapply a_tran.
  - apply ss_add2.
    apply lookup.
  - unfold  envXY, update.
    simpl.
    eapply a_tran.
    + apply ss_add1.
      apply lookup.
    + eapply a_tran.
      apply ss_add.
      reflexivity.
      simpl.
      apply a_refl.
Qed.

Create HintDb mydb.
Hint Constructors aeval_ss : mydb.
Hint Constructors a_clos : mydb.
Hint Unfold envXY : mydb.
Hint Unfold update : mydb.

Example e2_yx_test :
  "x" +' "y" -< envXY >* 21.
Proof.
  eauto 10 with mydb.
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
Reserved Notation "B -{ S }-> B'"  (at level 80).
Inductive beval : BExp -> Env -> BExp -> Type :=
| s_btrue : forall sigma, btrue -{ sigma }-> btrue
| s_bfalse : forall sigma, bfalse -{ sigma }-> bfalse
| not' : forall b b' sigma,
    b -{ sigma }-> b' ->
    !' b -{ sigma }-> !' b'
| notTrue : forall sigma,
    !' btrue -{ sigma }-> bfalse 
| notFalse : forall sigma,
    !' bfalse -{ sigma }-> btrue 
| and' : forall b1 b1' b2 sigma,
    b1 -{ sigma }-> b1' ->
    b1 &&' b2 -{ sigma }-> b1' &&' b2
| andTrue: forall b2 sigma,
    btrue &&' b2 -{ sigma }-> b2
| andFalse: forall b2 sigma,
    bfalse &&' b2 -{ sigma }-> bfalse 
| blt1: forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' -> 
  a1 <' a2 -{ sigma }-> a1' <' a2
| blt2: forall a2 a2' (i1 : nat) sigma,
  a2 -[ sigma ]-> a2' -> 
  i1 <' a2 -{ sigma }-> i1 <' a2'
| blt': forall i1 i2 sigma,
    num i1 <' num i2 -{ sigma }->
    if (Nat.ltb i1 i2) then btrue else bfalse
where "B -{ S }-> B'" := (beval B S B').

Reserved Notation "B1 -| S |-* B2"  (at level 63).
Inductive b_clos : BExp -> Env -> BExp
                   -> Type :=
| b_refl : forall b sigma, b -| sigma |-* b
| b_tran : forall b1 b2 b3 sigma,
  b1 -{ sigma }-> b2 ->
  b2 -| sigma |-* b3 -> 
  b1 -| sigma |-* b3
where "B1 -| S |-* B2" := (b_clos B1 S B2).



Definition env1 :=
  update
    (update
       (update env0 "i" 10)
       "j" 11)
    "n" 12.

Example e2 :
  ("i" <' "j" +' 4 &&' btrue) -| env1 |-* btrue.
Proof.
  eapply b_tran.
  - apply and'.
    + apply blt1.
      apply lookup.
  - eapply b_tran.
    + apply and'.
      apply blt2.
      eauto with mydb.
    + eapply b_tran.
      * apply and'.
        apply blt2.
        eauto with mydb.
      * eapply b_tran.
        apply and'.
        apply blt'.
        eapply b_tran.
        ** apply and'.
           simpl.
           apply s_btrue.
        ** eapply b_tran.
           apply andTrue.
           apply b_refl.
Qed.

Hint Constructors beval : mydb.
Hint Constructors b_clos : mydb.
Hint Unfold Nat.ltb : mydb.
Hint Unfold env1 : mydb.

Example e2' :
  ("i" <' "j" +' 4 &&' btrue) -| env1 |-* btrue.
Proof.
  eauto 15 with mydb.
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


Reserved Notation "[ S , E ]~>[ S' , E' ]" (at level 99).
Inductive eval : Stmt -> Env -> Stmt -> Env -> Type :=
| ss_assign1 : forall x a a' sigma,
    a -[ sigma ]-> a' ->
    (eval (assign x a) sigma (assign x a') sigma)
| ss_assign: forall sigma x (v: nat),
    (eval (assign x v) sigma skip (update sigma x v))
| seq1: forall s1 s1' s2 sigma,
  (eval s1 sigma s1' sigma) ->
  (eval (seq s1 s2) sigma (seq s1' s2) sigma)
| ss_seq: forall s2 sigma,
  (eval (seq skip s2) sigma s2 sigma)
.

