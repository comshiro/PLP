
(*
Un limbaj format din:
1. expresii aritmetice
2. expresii boolene
3. instructiuni: assignment, if-then-else, while, skip, sequences
 *)

Require Import String.
Open Scope string_scope.

Check "asdasf".

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp.


Check add (num 3) (var "x").

(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

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
| blt : AExp -> AExp -> BExp.

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
| assign : string -> AExp -> Stmt
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
Check seq ("s" ::= "s" +' "i")
  ("i" ::= "i" +' 1).

Notation "S1 ; S2" := (seq S1 S2)
                        (at level 99).
Check
  "s" ::= "s" +' "i" ;
"i" ::= "i" +' 1.


Definition sum :=
"n" ::= 10 ;
"i" ::= 0 ;
"s" ::= 0 ;
while ("i" <' "n" +' 1) (
    "s" ::= "s" +' "i" ;
    "i" ::= "i" +' 1
  ).
Check sum.