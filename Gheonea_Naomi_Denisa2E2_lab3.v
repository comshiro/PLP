Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.

Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

(*Scrieți o funcție le_Nat care primește doi parametri m și n de tip Nat și returnează true dacă m este mai mic sau egal decât n.*)


Fixpoint le_Nat(m n : Nat) : bool :=
match m with
| O =>true
|S m' => match n with
        | O=>false
        |S n' => le_Nat m' n'
        end
end.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)


(*Demonstrați următoarea lemă (hint: puteți utiliza induction și inversion):*)
Lemma le_then_O :
  forall n,
    le_Nat n O = true ->
    n = O.
Proof.
  intro n.
  induction n.
  simpl. reflexivity.
  intros H.
  simpl in H.
  inversion H.
Qed.

(*Demonstrați următoarele leme prin inducție:*)
Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
    intro x.
    induction x.
    simpl. reflexivity.
    apply IHx.
Qed.

Lemma le_Trans:
forall m n p,
  le_Nat m n = true->
  le_Nat n p = true->
  le_Nat m p = true.
Proof.
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

(*Formulați si demonstrați prin inducție în Coq proprietatea: x este mai mic sau egal decât x + y, pentru orice x și y.*)
Lemma ex4 :
  forall x y,
    le_Nat x (add x y) = true.
Proof.
  intros x y.
  induction x.
  simpl. reflexivity.
  apply IHx.
Qed.

(*Dacă x este mai mic sau egal decât y, atunci x este mai mic decât y + z, pentru orice numere naturale x, y și z. Formulați această proprietate ca lemă în Coq și demonstrați-o prin inducție.*)
Lemma ex5:
  forall x y z,
    (le_Nat x y = true) -> 
    (le_Nat x (add y z) = true).
Proof.
  intros x y z H.
  induction x.
  simpl. reflexivity.
  destruct y.
  simpl.
  destruct z.
  simpl in H. 
  inversion H.
  

  
(*Dacă x este mai mic sau egal decât y, atunci maximul dintre x și y este mereu y, pentru orice numere naturale x și y. Formulați această proprietate ca lemă în Coq și demonstrați-o prin inducție.*)
Lemma ex6:
  forall x y,
  (le_Nat x y = true) -> (le_Nat x y = true).
Proof.
  intros x y H.
  apply H.
Qed.

Lemma ex6':
  forall x y,
  (le_Nat x y = true) -> ((max x y) = y).
Proof.
  intros x y H.
  induction x.
  simpl. reflexivity.
  destruct y.
  simpl. inversion H.
Qed.

(*Dacă x nu este mai mic sau egal decât y, atunci maximul dintre x și y este mereu x, pentru orice numere naturale x și y.*)
Lemma ex7:
  forall x y,
  (le_Nat x y = false) -> ((max x y) = x).
 Proof.
  intros x y H.
  induction x.
  simpl.
  destruct y.
  simpl. inversion H.
  inversion H.
  


  
  
