Require Import String.
Open Scope string_scope.


Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| bor : Cond -> Cond -> Cond.
Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.
Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.
Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).

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
Inductive exp_eval_ss : Exp -> Env -> Exp -> Type :=
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
(*| ss_mul1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 *' a2) -[ sigma ]-> a1' *' a2
| ss_mul2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 *' a2) -[ sigma ]-> a1 *' a2'
| ss_mul : forall (i1 i2 : nat) sigma,
  (i1 *' i2) -[ sigma ]-> i1 * i2 *)
| ss_sub1 : forall e1 e1' e2 sigma,
    e1 -[ sigma ]-> e1' ->
    (sub e1 e2) -[ sigma ]-> (sub e1' e2)
| ss_sub2 : forall n1 e2 e2' sigma,
    e2 -[ sigma ]-> e2' ->
    (sub (num n1) e2) -[ sigma ]-> (sub (num n1) e2')
| ss_sub : forall n1 n2 sigma,
    (sub (num n1) (num n2)) -[ sigma ]-> (num (n1 - n2))
| ss_div1 : forall e1 e1' e2 sigma,
    e1 -[ sigma ]-> e1' ->
    (div e1 e2) -[ sigma ]-> (div e1' e2)
| ss_div2 : forall n1 e2 e2' sigma,
    e2 -[ sigma ]-> e2' ->
    (div (num n1) e2) -[ sigma ]-> (div (num n1) e2')
| ss_div : forall n1 n2 sigma,
    n2 <> 0 -> 
    (div (num n1) (num n2)) -[ sigma ]-> (Nat.div n1 n2)
where "A -[ S ]-> V" := (exp_eval_ss A S V).


Reserved Notation "A -< S >* V"  (at level 61).
Inductive a_clos : Exp -> Env -> Exp
                   -> Type :=
| a_refl : forall a sigma, a -< sigma >* a
| a_tran : forall a1 a2 a3 sigma,
  a1 -[ sigma ]-> a2 ->
  a2 -< sigma >* a3 -> 
  a1 -< sigma >* a3
where "A -< S >* V" := (a_clos A S V).

Example add_example :
  (var "x" +' num 3) -[ update env0 "x" 5 ]-> (num 5 +' num 3).
Proof.
  apply ss_add1.
  apply lookup.
Qed.


Example div_example :
  (div (num 10) (num 2)) -[ env0 ]-> (num 5).
Proof.
  apply ss_div.
  intro H.
  inversion H.
Qed.


Reserved Notation "C =[ S ]=> B" (at level 60).

Inductive cond_eval_ss : Cond -> Env -> bool -> Type :=
| ss_base : forall b sigma,
    (base b) =[ sigma ]=> b
| ss_bnot : forall c sigma b,
    c =[ sigma ]=> b -> 
    (bnot c) =[ sigma ]=> negb b
| ss_beq1 : forall e1 e1' e2 sigma,
    e1 =[ sigma ]=> e1' -> 
    (beq e1 e2) =[ sigma ]=> (beq e1' e2)
| ss_beq2 : forall n1 e2 e2' sigma,
    e2 =[ sigma ]=> e2' -> 
    (beq (num n1) e2) =[ sigma ]=> (beq (num n1) e2')
| ss_beq : forall n1 n2 sigma,
    (beq (num n1) (num n2)) =[ sigma ]=> (num (n1 =? n2))
| ss_less1 : forall e1 e1' e2 sigma,
    e1 =[ sigma ]=> e1' -> 
    (less e1 e2) =[ sigma ]=> (less e1' e2)
| ss_less2 : forall n1 e2 e2' sigma,
    e2 =[ sigma ]=> e2' -> 
    (less (num n1) e2) =[ sigma ]=> (less (num n1) e2')
| ss_less : forall n1 n2 sigma,
    (less (num n1) (num n2)) =[ sigma ]=> (num (n1 <? n2))
| ss_bor1 : forall c1 c1' c2 sigma,
    c1 =[ sigma ]=> c1' -> 
    (bor c1 c2) =[ sigma ]=> (bor c1' c2)
| ss_bor2 : forall b1 c2 c2' sigma,
    c2 =[ sigma ]=> c2' -> 
    (bor (base b1) c2) =[ sigma ]=> (bor (base b1) c2')
| ss_bor : forall b1 b2 sigma,
    (bor (base b1) (base b2)) =[ sigma ]=> (base (b1 || b2))
where "C =[ S ]=> B" := (cond_eval_ss C S B).
