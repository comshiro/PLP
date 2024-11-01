(*Definiți un tip de date algebric pentru zilele săptămânii.*)
Inductive Day:=
|Monday
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

Definition next_day (d : Day) : Day :=
  match d with
  |Monday=>Tuesday
  |Tuesday=>Wednesday
  |Wednesday=>Thursday
  |Thursday=>Friday
  |Friday=>Saturday
  |Saturday=>Sunday
  |Sunday=>Monday
  end.

Compute next_day Monday
(*Definiți o funcție de egalitate peste acest tip de date.*)
