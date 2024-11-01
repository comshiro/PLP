Require Import String.
Open Scope string_scope.
Check "asdaf".

Inductive Exp : Type :=
| num : nat -> Exp
| add : Exp -> Exp -> Exp
| mul : Exp -> Exp -> Exp
|var : string -> Exp.

Check (num 1).
Check (num 2).
Check (add (num 1) (num 2)).
Check (add (num 1) (mul (num 2) (num 3))).

Coercion num : nat >-> Exp.
Check (add 1 2).

Set Printing Coercions.
Check (add 1 2).
Check (add 1 (mul 2 3)).

Notation "X +^ Y" := (add X Y ) (at level 50, left associativity).
Notation "X *^ Y" := (mul X Y ) (at level 40, left associativity).

Check 1 +^ 2.
Check 1 +^ 2 *^ 3.

Set Printing All.
Check 1 +^ 2.
Check 1 +^ 2 *^ 3.
Unset Printing All.

Declare Custom Entry exp.
Declare Scope exp_scope.
Notation "<[ E ]>" := E (at level 0, E custom exp at level 99) : exp_scope.
Notation "( x )" := x (in custom exp, x at level 99) : exp_scope.
Notation "x" := x (in custom exp at level 0, x constr at level 0) : exp_scope.
Notation "f x .. y" := (.. (f x ) .. y)
(in custom exp at level 0, only parsing,
f constr at level 0, x constr at level 9,
y constr at level 9) : exp_scope.
Notation "X + Y" := (add X Y ) (in custom exp at level 50, left associativity).
Notation "X * Y" := (mul X Y ) (in custom exp at level 40, left associativity).

Open Scope exp_scope.
Check <[ 1 + 2 * 3 ]>.
Check <[ (1 + 2) * 3 ]>.
Close Scope exp_scope.


Check add (num 3) (var "x").


Coercion var : string >-> Exp.

Check add 3 "x".
Set Printing Coercions.
Check add 3 "x".
Unset Printing Coercions.
Check add 3 "x".

Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).
Notation "A *' B" :=
  (mul A B)
    (left associativity, at level 40).


Check 2 +' 5.
Check "x" +' 5 +' "y".
Set Printing Parentheses.
Check "x" +' 5 +' "y".

Check "x" +' 5 *' "y".
Check "x" *' 5 +' "y".

Print bool.
(* boolean *)
Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| band : BExp -> BExp -> BExp
| bnot : BExp -> BExp
| blt : Exp -> Exp -> BExp.

Notation "B1 &&' B2" :=
  (band B1 B2) (left associativity,
      at level 65).
Notation "!' B" :=
  (bnot B) (at level 62).
Notation "A1 <' A2" :=
  (blt A1 A2)
    (at level 60).

Check "i" <' "n".
Check "i" +' 1 <' 5 *' "j" +' 4 &&' btrue.


Check 2 *' (3 +' 5).


Inductive Stmt :=
| assign : string -> Exp -> Stmt
| ite : BExp -> Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt.

Check (assign "n" 10).
Check (assign "i" 0).
Check (assign "s" ("s" +' "i")).

Notation "X ::= A" := (assign X A)
                        (at level 90).
Check "n" ::= 10.
Check "i" ::= 0.
Check "s" ::= "s" +' "i".

Check ite ("i" <' "n")
          ( "i" ::= "i" +' 1)
          ( "i" ::= "i" *' 1).

Check while ("i" <' "n")
  ("s" ::= "s" +' "i").

Check skip.