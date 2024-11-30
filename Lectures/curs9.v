Require Import String.

Inductive Exp :=
| anum : nat -> Exp
| avar : string -> Exp
| aplus : Exp -> Exp -> Exp
| amult : Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| blessthan : Exp -> Exp -> Exp.
                          
Coercion anum : nat >-> Exp.
Coercion avar : string >-> Exp.
Notation "A +' B" := (aplus A B) (at level 50, left associativity).
Notation "A *' B" := (amult A B) (at level 40, left associativity).
Notation "A <' B" := (blessthan A B) (at level 60).
Notation "A &&' B" := (band A B) (at level 750, left associativity).


Check 2 +' 2.
Check 2 +' btrue.
Check 2 +' (4 <' 3).



Definition Env := string -> nat.
Definition update
           (sigma : Env)
           (x : string)
           (v : nat) : Env :=
  fun y => if eqb x y
           then v
           else (sigma y).


Reserved Notation "A -[ S ]-> B"
         (at level 90).


Inductive eval :
  Exp -> Env -> Exp -> Prop :=
| const : forall i sigma,
    (anum i) -[ sigma ]-> i
| lookup : forall x sigma,
    (avar x) -[ sigma ]-> (sigma x)
| add_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 +' a2) -[ sigma ]-> (a1' +' a2)
| add_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 +' a2) -[ sigma ]-> (a1 +' a2')
| add : forall i1 i2 sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n
| mul_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 *' a2) -[ sigma ]-> (a1' *' a2)
| mul_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 *' a2) -[ sigma ]-> (a1 *' a2')
| mul : forall i1 i2 sigma n,
    n = i1 * i2 -> 
    (i1 *' i2) -[ sigma ]-> n
| etrue : forall sigma,
  btrue -[ sigma ]-> btrue
| efalse : forall sigma,
  bfalse -[ sigma ]-> bfalse
| lessthan_l : forall a1 a2 sigma a1',
    a1 -[ sigma ]-> a1' ->
    (a1 <' a2) -[ sigma ]-> (a1' <' a2)
| lessthan_r : forall a1 a2 sigma a2',
    a2 -[ sigma ]-> a2' ->
    (a1 <' a2) -[ sigma ]-> (a1 <' a2')
| lessthan_ : forall i1 i2 sigma b,
    b = (if Nat.ltb i1 i2 then btrue else bfalse) -> 
    (i1 <' i2) -[ sigma ]-> b
| not_1: forall b b' sigma,
    b -[ sigma ]-> b' ->
    (bnot b) -[ sigma ]-> (bnot b')
| not_t : forall sigma,
    (bnot btrue) -[ sigma ]-> bfalse
| not_f : forall sigma,
    (bnot bfalse) -[ sigma ]-> btrue
| band_1 : forall b1 b2 b1' sigma,
    b1 -[ sigma ]-> b1' ->
    (band b1 b2) -[ sigma ]-> (band b1' b2)
| band_true : forall b2 sigma,
    (band btrue b2) -[ sigma ]-> b2
| band_false : forall b2 sigma,
  (band bfalse b2) -[ sigma ]-> b2
where "A -[ S ]-> B" := (eval A S B).

Reserved Notation "A -[ S ]>* B"
         (at level 90).
Inductive eval_closure :
  Exp -> Env -> Exp -> Prop :=
| refl : forall e sigma,
    e -[ sigma ]>* e
| tran : forall e1 e2 e3 sigma,
  e1 -[ sigma ]-> e2 ->
  e2 -[ sigma ]>* e3 ->
  e1 -[ sigma ]>* e3      
where "A -[ S ]>* B" :=
  (eval_closure A S B).

Create HintDb types.
Hint Constructors Exp : types.
Hint Constructors eval : types.
Hint Constructors eval_closure : types.

Definition Env0 : Env := fun x => 0.

Hint Unfold Env0 : types.
Hint Unfold update : types.

Open Scope string_scope.

Example e1 : 2 +' "x" -[ Env0 ]>* 2.
Proof.
  eapply tran.
  - apply add_r.
    apply lookup.
  - eapply tran.
    + unfold Env0.
      apply add.
      reflexivity.
    + simpl. apply refl.
Qed.


Example e2 : 2 +' btrue -[ Env0 ]>* 2.
Proof.
  eapply tran.
  - apply add_r.
    apply etrue.
  - eapply tran.
    + (* can't prove this *)
Abort.


(* Types *)
Print Exp.

Inductive Typ := Nat | Bool.
Hint Constructors Typ : types.

Print Exp.
Inductive type_of : Exp -> Typ -> Prop :=
| t_num : forall n, type_of (anum n) Nat
| t_var : forall x, type_of (avar x) Nat
| t_add : forall e1 e2,
  type_of e1 Nat ->
  type_of e2 Nat ->
  type_of (e1 +' e2) Nat
| t_mul : forall e1 e2,
  type_of e1 Nat ->
  type_of e2 Nat ->
  type_of (e1 *' e2) Nat
| t_true : type_of btrue Bool
| t_false : type_of bfalse Bool
| t_not : forall b,
    type_of b Bool ->
    type_of (bnot b) Bool
| t_and : forall e1 e2,
  type_of e1 Bool ->
  type_of e2 Bool -> 
  type_of (e1 &&' e2) Bool 
| t_less: forall e1 e2,
  type_of e1 Nat ->
  type_of e2 Nat -> 
  type_of (e1 <' e2) Bool.

Hint Constructors type_of : types.


Example e3 :
  type_of (2 +' "x") Nat.
Proof.
  apply t_add.
  - apply t_num.
  - apply t_var.
Qed.

Example e4 :
  type_of (2 +' btrue) Nat.
Proof.
  apply t_add.
  - apply t_num.
  - (* can't prove this *)
Abort.


Inductive nat_value : Exp -> Prop :=
| n_val : forall n, nat_value (anum n).

Inductive bool_value : Exp -> Prop :=
| t_val : bool_value btrue
| f_val : bool_value bfalse.

Definition value (e : Exp) :=
  nat_value e \/ bool_value e.

Lemma bool_canonical :
  forall b,
    type_of b Bool ->
    value b ->
    bool_value b.
Proof.
  intros b H H'.
  inversion H'; try assumption.
  inversion H0.
  rewrite <- H1 in H.
  inversion H.
Qed.

Lemma nat_canonical :
  forall n,
    type_of n Nat ->
    value n ->
    nat_value n.
Proof.
  intros n H H'.
  inversion H'; try assumption.
  inversion H0.
  - rewrite <- H1 in H.
    inversion H.
  - rewrite <- H1 in H.
    inversion H.
Qed.

Theorem progress:
  forall e T sigma,
    type_of e T ->
    (value e \/ exists e', e -[ sigma ]-> e').
Proof.
  intros e T sigma H.
  induction H.
  - left.
    unfold value.
    left.
    apply n_val.
  - right.
    exists (sigma x).
    apply lookup.
  - right.
    destruct IHtype_of1 as [H1 | [e' He']].
    destruct IHtype_of2 as [H2 | [e'' He'']].
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    inversion H.
    inversion H0.
    eexists.
    apply add.
    reflexivity.
    eexists.
    apply add_r.
    exact He''.
    eexists.
    apply add_l.
    exact He'.
  - right.
    destruct IHtype_of1 as [H1 | [e' He']].
    destruct IHtype_of2 as [H2 | [e'' He'']].
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    inversion H.
    inversion H0.
    eexists.
    apply mul.
    reflexivity.
    eexists.
    apply mul_r.
    exact He''.
    eexists.
    apply mul_l.
    exact He'.
  - left. unfold value. right. apply t_val.
  - left. unfold value. right. apply f_val.
  - right.
    destruct IHtype_of as [H' | [e' He']].
    + apply bool_canonical in H; auto.
      inversion H.
      * exists bfalse. 
        apply not_t.
      * exists btrue.
        apply not_f.
    + exists (bnot e').
      apply not_1.
      exact He'.
  - destruct IHtype_of1 as [H1 | [e' He']].
    + apply bool_canonical in H; auto.
      inversion H.
      * right.
        exists e0.
        apply band_true.
      * right.
        exists e0.
        apply band_false.
    + right.
      exists (e' &&' e0).
      apply band_1.
      exact He'.
  - right.
    destruct IHtype_of1 as [H1 | [e' He']].
    destruct IHtype_of2 as [H2 | [e'' He'']].
    apply nat_canonical in H; auto.
    apply nat_canonical in H0; auto.
    inversion H.
    inversion H0.
    eexists.
    apply lessthan_.
    reflexivity.
    eexists.
    apply lessthan_r.
    exact He''.
    eexists.
    apply lessthan_l.
    exact He'.
Qed.

Theorem preservation:
  forall e T e' sigma,
    type_of e T ->
    e -[ sigma ]-> e' ->
    type_of e' T.
Proof.
  intros e T e' sigma H H'.
  revert e' H'.
  induction H; intros; inversion H'; subst; eauto with types.
  
  
