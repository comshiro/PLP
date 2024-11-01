(*Definiți un tip de date algebric pentru zilele săptămânii.*)
Inductive Day:=
|Monday (*constructori*)
|Tuesday
|Wednesday
|Thursday
|Friday
|Saturday
|Sunday.

Print Day.
Print Monday.
Check Monday.
Print bool.
Check false.
Check true.

(*Definiți o funcție care returnează ziua următoare. *)
Definition next_day (d:Day) : Day :=
  match d with
  |Monday=>Tuesday
  |Tuesday=>Wednesday
  |Wednesday=>Thursday
  |Thursday=>Friday
  |Friday=>Saturday
  |Saturday=>Sunday
  |Sunday=>Monday
  end.

Compute (next_day Monday).
Check next_day.
Print next_day.

(*Definiți o funcție de egalitate peste acest tip de date.*)

Definition equal(d1 d2 : Day) : bool :=
  match d1,d2 with
  |Monday,Monday =>true
  |Tuesday,Tuesday=>true
  |Wednesday,Wednesday=>true
  |Thursday,Thursday=>true
  |Friday,Friday=>true
  |Saturday,Saturday=>true
  |Sunday,Sunday=>true
  |_, _ =>false
  end.

Compute equal Monday Monday.
Compute equal Monday Friday.

Scheme Equality for Day.
Print Day_beq.

(*Definiți tipul de date boolean.*)
Inductive Boolean: Type :=
  |tt
  |ff.

(*Definiți funcțiile: negație, conjuncție, disjuncție peste tipul de date boolean definit la exercițiul precedent. *)

Definition neg (a : bool) : bool :=
  match a with
  |true=>false
  |false=>true
  end.

Definition conj (a b: bool) : bool :=
  match a, b with
  |true, true=>true
  |false, false=>false
  |_,_=>false
  end.

Definition disj (a b: bool) : bool :=
  match a, b with
  |false, false=>false
  |_,_=>true
  end.

(*Bonus*)


Print nat. 

Inductive byte :=
|B: bool-> bool -> bool -> bool -> bool -> bool -> bool -> bool->byte.

Check (B true false false false false false false false).

Definition add_bit (b1 b2 carry: bool) : bool * bool :=
  match b1, b2, carry with
  | false, false, false => (false, false)
  | false, false, true  => (true, false)
  | false, true, false  => (true, false)
  | false, true, true   => (false, true)
  | true, false, false  => (true, false)
  | true, false, true   => (false, true)
  | true, true, false   => (false, true)
  | true, true, true    => (true, true)
  end.

Definition add_bytes(b1 b2: byte) : byte :=
  match b1, b2 with
  | B b0 b1 b2 b3 b4 b5 b6 b7, B c0 c1 c2 c3 c4 c5 c6 c7 =>
    let (d0, carry) := add_bit b0 c0 false in
    let (d1, carry) := add_bit b1 c1 carry in
    let (d2, carry) := add_bit b2 c2 carry in
    let (d3, carry) := add_bit b3 c3 carry in
    let (d4, carry) := add_bit b4 c4 carry in
    let (d5, carry) := add_bit b5 c5 carry in
    let (d6, carry) := add_bit b6 c6 carry in
    let (d7, carry) := add_bit b7 c7 carry in
  if carry then
    B false false false false false false false false (*Am decis sa returnez zero daca adunarea nu este valida.*)
  else
    B d0 d1 d2 d3 d4 d5 d6 d7
end.


Check byte.
Print byte.
Check B.

Definition sub_bit (b1 b2 borrow: bool) : bool * bool :=
  match b1, b2, borrow with
  | false, false, false => (false, false)
  | true, false, false => (true, false)
  | true, false, true => (false, false)
  | false, true, false => (true,true)
  | false, true, true => (false, true) (*!!!*)
  | true, true, false => (false, false)
  | true, true, true => (true, true)
  | false, false, true => (false, false)
  end.

Definition sub_bytes (b1 b2: byte) : byte := (*de tratat cazul in care nu ne putem imprumuta de la cel mai apropiat true*)
  match b1, b2 with
  | B b0 b1 b2 b3 b4 b5 b6 b7, B c0 c1 c2 c3 c4 c5 c6 c7 =>
    let (d0, borrow) := sub_bit b0 c0 false in
    let (d1, borrow) := sub_bit b1 c1 borrow in
    let (d2, borrow) := sub_bit b2 c2 borrow in
    let (d3, borrow) := sub_bit b3 c3 borrow in
    let (d4, borrow) := sub_bit b4 c4 borrow in
    let (d5, borrow) := sub_bit b5 c5 borrow in
    let (d6, borrow) := sub_bit b6 c6 borrow in
    let (d7, borrow) := sub_bit b7 c7 borrow in
   if borrow then
    B false false false false false false false false
   else
    B d0 d1 d2 d3 d4 d5 d6 d7
  end.

(*

Fixpoint inmultire(b1 b2 : byte) :byte :=
match b1, b2 with
|b1, (B false false false false false false false true) => b1
|b1, B false false false false false false false false => 
B false false false false false false false false
|b1, b2 => 
  let b1 := (add_bytes b1 b1) in
  let b2 := sub_bytes b2 (B false false false false false false false true) in
  inmultire b1 b2
end.
*)

Definition unu : byte := B false false false false false false false true.
Definition zero : byte := B false false false false false false false false.

Fixpoint inmultire(b1 b2 : byte) :byte :=
match b1, b2 with
|b1, unu => b1
|b1,b2=>
  let b1 := (add_bytes b1 b1) in
  let b2 := (sub_bytes b2 unu) in
  inmultire b1 b2
end.




