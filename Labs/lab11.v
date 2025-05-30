Require Import String.

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Inductive BExp :=
| btrue : BExp                      (* valoarea adevărată *)
| bfalse : BExp                     (* valoarea falsă *)
| bnot : BExp -> BExp               (* negare logică *)
| band : BExp -> BExp -> BExp       (* și logic *)
| blessthan : AExp -> AExp -> BExp  (* mai mic decât *)
| bgreaterthan : AExp -> AExp -> BExp. (* mai mare decât *)

Inductive Cond :=
| base : BExp -> Cond               
| beq : AExp -> AExp -> Cond        (* egalitate între expresii aritmetice *)
| less : AExp -> AExp -> Cond       (* mai mic decât *)
| andCond : Cond -> Cond -> Cond.  

Inductive Stmt :=
| skip : Stmt                              (* nu face nimic *)
| assign : string -> AExp -> Stmt          (* atribuirea unei valori unei variabile *)
| seq : Stmt -> Stmt -> Stmt               (* secvențierea a două instrucțiuni *)
| ite : Cond -> Stmt -> Stmt -> Stmt       (* if-then-else *)
| while : Cond -> Stmt -> Stmt             (* buclă while *)
| methodCall : string -> string -> list AExp -> Stmt. 


Inductive ClassDecl :=
| class : string -> list (string * AExp) -> list (string * Stmt) -> ClassDecl.

Definition PointClass :=
  class "Point"
    [("x", Public, num 0); ("y", Public, num 0)]  (* Attributes with Public access *)
    [("move", Public, seq (assign "x" (var "new_x"))
                          (assign "y" (var "new_y")))]. (* Methods with Public access *)


Inductive Obj :=
| obj : string -> string -> Obj.

Definition InstantiatePoint :=
  obj "p" "Point".




Inductive MethodCall :=
| call : string -> string -> list AExp -> Stmt.
