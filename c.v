(*Definiți un tip de date algebric pentru zilele săptămânii.*)
Inductive day: Type:=
|Monday
|Tuesday
|Wednesday
|Thursday
|Friday
|Saturday
|Sunday.

Definition x := Monday.

Check x.

(*Definiți o funcție de egalitate peste acest tip de date.*)
Definition eqday (a:day) : day :=
  match a with
  |Monday=>Monday
  |Tuesday=>Tuesday
  |Wednesday=>Wednesday
  |Thursday=>Thursday
  |Friday=>Friday
  |Saturday=>Saturday
  |Sunday=>Sunday
  end.

(*Definiți o funcție care returnează ziua următoare.*)

Definition nextday (b:day) : day :=
  match b with
  |Monday=>Tuesday
  |Tuesday=>Wednesday
  |Wednesday=>Thursday
  |Thursday=>Friday
  |Friday=>Saturday
  |Saturday=>Sunday
  |Sunday=>Monday
  end.

(*Definiți tipul de date boolean.*)
Inductive bool: Type :=
  |true
  |false.

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

