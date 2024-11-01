Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint le_Nat(m n : Nat) : bool :=
match m with
| O =>true
|S m' => match n with
        | O=>false
        |S n' => le_Nat m' n'
        end
end.

Compute le_Nat O (S O).

Lemma le_Trans:
forall m n p,
  le_Nat m n = true->
  le_Nat n p = true->
  le_Nat m p = true.
Proof.
  (*intros m n p H1 H2.*)
  induction m.
   -simpl. reflexivity.
   -intros n p H1 H2.
    simpl.
    destruct p.
     +simpl in *.
      destruct n.
      assumption.
      simpl in H2.
      assumption.
     +simpl in H1.
      destruct n.
      ++inversion H1.
      ++simpl in H2.
        apply IHm with (n:=n).
        exact H1.
        exact H2.
Qed.
(*
Inductive ListNat:=
|Nil'' : ListNat
|Cons'':Nat -> ListNat -> ListNat.

Compute Nil''.
Compute (Cons'' (S O) Nil'').


Inductive Listbool:=
|Nil' : Listbool
|Cons' : bool -> Listbool -> Listbool.*)

(*Polymorphism*)
Inductive List(T:Type) :=
|Nil : List T
|Cons : T -> List T-> List T.


Check Nil.
Check Cons.

Definition ListNat := List Nat.
Compute (Cons Nat O
          (Cons Nat (S O) (Nil Nat))).

Definition ListBool := List bool.
Compute (Cons bool true
          (Cons bool false (Nil bool))).

(*Implicit Arguments*)

Arguments Nil {T}.
Arguments Cons {T}.

Print nat.

Compute (Cons O (Cons (S O)(Nil))).

Fixpoint length {T:Type} (l : List T) : nat :=
match l with
|Nil => 0
|Cons e l' => 1 + length l'
end.

(*High-order functions*)

Fixpoint filter 
  {T :Type}
  (l : List T)
  (f : T->bool) :=
match l with
|Nil=>Nil
|Cons x l' => if (f x)
                then Cons x (filter l' f)
                else (filter l' f)
end.

Definition myList :=
(Cons 2 (Cons 7 (Cons 20(Cons 14(Cons 12 Nil))))).

Check myList.
Locate "<=?".

(*
  Check Nat. leb.
  Print Nat.leb.
  Print Nat.

*)
Definition is_digit (n:nat) : bool :=
if Nat.leb n 9
then true
else false.

Compute is_digit 10.
Compute is_digit 2.

Compute filter myList is_digit.
Check Nat.even.
Compute filter myList Nat.even.

Definition compose {A B C : Type}
  (f : B -> C)
  (g : A -> B)
  : A -> C :=
  fun x => f( g x).

Compute (compose (fun x => x*2) (fun x => x+5)) 10.

(*Proofs*)

Lemma conj_vs_impl:
  forall P Q R,
    (P -> Q -> R) <->
    (P /\Q -> R).
Proof.
  split.
  intros H (H1 & H2).
   apply H; assumption.
   intros H H1 H2.
   apply H.
   split; assumption.
Qed.

Check bool.
Check Prop.

Check 10 = 10.
Check Nat.eqb 10 10.

Compute Nat.eqb 10 10.

Compute 10 = 10.
Compute 10=11.

Goal 10=10.
  reflexivity.
Qed.

Goal 10=11.
  Abort.

