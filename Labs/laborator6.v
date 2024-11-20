Require Import String.
Require Import Lia.
Open Scope string_scope.

Definition Env := string -> nat.
Definition env0 : Env := fun x => 0.

Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.

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


Reserved Notation "E =[ S ]=> N" (at level 60).
Inductive exp_eval : Exp -> Env -> nat -> Prop :=
| const : forall n sigma, 
    (num n) =[ sigma ]=> n
| lookup : forall x sigma, 
    (var x) =[ sigma ]=> (sigma x)
| bs_add : forall e1 e2 sigma n1 n2 n,
    e1 =[ sigma ]=> n1 ->
    e2 =[ sigma ]=> n2 ->
    n = n1 + n2 ->
    (add e1 e2) =[ sigma ]=> n
| bs_sub : forall e1 e2 sigma n1 n2 n,
    e1 =[ sigma ]=> n1 ->
    e2 =[ sigma ]=> n2 ->
    (n1 >= n2) -> 
    n = n1 - n2 ->
    (sub e1 e2) =[ sigma ]=> n
| bs_div : forall e1 e2 sigma n1 n2 n,
    e1 =[ sigma ]=> n1 ->
    e2 =[ sigma ]=> n2 ->
    (n2 <> 0) ->
    n = Nat.div n1 n2 ->
    (div e1 e2) =[ sigma ]=> n
where "E =[ S ]=> N" := (exp_eval E S N).


Example e1 : sub (var "x") (num 3) =[ update env0 "x" 5 ]=> 2.
Proof.
  eapply bs_sub with (n1 := 5) (n2 := 3).
  apply lookup.
  apply const.
  lia.
  reflexivity.
Qed.


(*
Example e2 : sub (var "x") (num 3) =[ update env0 "x" 1 ]=> 2.
Proof.
  eapply bs_sub with (n1 := 5) (n2 := 3).
  apply lookup.
  apply const.
  lia.
  reflexivity.
Qed.

Nu se poate demonstra :)))

*)

Print Nat.eqb.
Reserved Notation "C ~[ S ]~> B" (at level 60).
Inductive cond_eval : Cond -> Env -> bool -> Prop :=
| bs_base : forall b sigma,
    base b ~[ sigma ]~> b
| bs_bnot : forall c sigma b,
    c ~[ sigma ]~> b ->
    bnot c ~[ sigma ]~> negb b
(*| bs_beq : forall e1 sigma n1,
    e1 =[ sigma ]=> n1
| bs_beq2: forall e2 sigma n2,
    e2 =[ sigma ]=> n2
| bs_beq3: forall e1 e2 sigma n1 n2,
    beq e1 e2 ~[ sigma ]~> (n1 =? n2)
*)
|bs_beq : forall e1 e2 sigma n1 n2,
    e1 =[ sigma ]=> n1 ->
    e2 =[ sigma ]=> n2 ->
    (n1 =? n2) = true -> 
     beq e1 e2 ~[ sigma ]~> true
| bs_less : forall e1 e2 sigma n1,
    e1 =[ sigma ]=> n1 ->
    less e1 e2 ~[ sigma ]~> less n1 e2
|bs_less2: forall e2 sigma n1,
    e2 =[sigma]=> n2 ->
    b=Nat.ltb n1 n2 = true ->
    less n1 e2 ~[sigma]~> true
| bs_bor_true : forall c1 c2 sigma,
    c1 ~[ sigma ]~> true ->
    bor c1 c2 ~[ sigma ]~> true
| bs_bor_false : forall c1 c2 sigma b,
    c1 ~[ sigma ]~> false ->
    c2 ~[ sigma ]~> b ->
    bor c1 c2 ~[ sigma ]~> b
where "C ~[ S ]~> B" := (cond_eval C S B).
(* NU IMI IESE https://media.tenor.com/3BsRwqoPs_MAAAAM/z%C5%82o%C5%9B%C4%87.gif *)

Reserved Notation "S -[ E ]-> E'" (at level 99).
Inductive eval : Stmt -> Env -> Env -> Type :=
| b_assign : forall x a v sigma sigma',
  a =[ sigma ]=> v ->
  sigma' = update sigma x v -> 
  (x ::= a) -[ sigma ]-> sigma'
| b_seq : forall s1 s2 sigma1 sigma2 sigma3,
  s1 -[ sigma1 ]-> sigma2 ->
  s2 -[ sigma2 ]-> sigma3 -> 
  (s1 ; s2) -[ sigma1 ]-> sigma3
(*
| while_t : forall b s sigma sigma',
  b ~[ sigma ]~> true ->
  (s ; while b s) -[ sigma ]-> sigma' ->
  (while b s) -[ sigma ]-> sigma'
| while_f : forall b s sigma,
  b ~[ sigma ]~> false ->
  (while b s) -[ sigma ]-> sigma 
*)
| ite_t : forall b sigma sigma' s1 s2,
  b ~[ sigma ]~> true ->
  s1 -[ sigma ]-> sigma' ->
  (ite b s1 s2) -[ sigma ]-> sigma'
| ite_f : forall b sigma sigma' s1 s2,
  b ~[ sigma ]~> false ->
  s2 -[ sigma ]-> sigma' ->
  (ite b s1 s2) -[ sigma ]-> sigma'
| it : forall b sigma sigma' s,
      b ~[ sigma ]~> true -> 
      s -[ sigma ]-> sigma' -> 
      (it b s) -[ sigma ]-> sigma'
| dowhile : forall s b sigma sigma',
      s -[ sigma ]-> sigma' -> 
      b ~[ sigma' ]~> true -> 
      (dowhile s b) -[ sigma ]-> sigma' -> 
      (dowhile s b) -[ sigma ]-> sigma'.
where "S -[ E ]-> E'" := (eval S E E').


