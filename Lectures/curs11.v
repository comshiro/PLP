Require Import String.
Open Scope string_scope.
Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Inductive BExp :=
| btrue : BExp                      
| bfalse : BExp                     
| bnot : BExp -> BExp             
| band : BExp -> BExp -> BExp      
| blessthan : AExp -> AExp -> BExp 
| bgreaterthan : AExp -> AExp -> BExp. 

Inductive Cond :=
| base : BExp -> Cond               
| beq : AExp -> AExp -> Cond        
| less : AExp -> AExp -> Cond       
| andCond : Cond -> Cond -> Cond.  

Inductive Stmt :=
| skip : Stmt                           
| assign : string -> AExp -> Stmt          
| seq : Stmt -> Stmt -> Stmt            
| ite : Cond -> Stmt -> Stmt -> Stmt 
| while : Cond -> Stmt -> Stmt            
| methodCall : string -> string -> list AExp -> Stmt. 

Inductive AccessModifier := 
| public : AccessModifier
| private : AccessModifier
| protected : AccessModifier.


Inductive ClassDecl :=
| class : string -> list (string * AExp) -> list (string * Stmt) -> ClassDecl.

Definition PointClass :=
  class "Point"
    (cons ("x", num 0) (cons ("y", num 0) nil)) (* Atribute *)
    (cons ("move", seq (assign "x" (var "new_x"))
                       (assign "y" (var "new_y"))) nil). (* Metode *)

Inductive Obj :=
| obj : string -> string -> Obj.

Definition InstantiatePoint :=
  obj "p" "Point".

Definition MovePoint :=
  methodCall "p" "move" (cons (num 5) (cons (num 10) nil)).


Definition RectangleClass :=
  class "Rectangle"
    (cons ("width", num 0) (cons ("height", num 0) nil)) (* Atribute *)
    (cons ("resize", seq (assign "width" (var "new_width"))
                         (assign "height" (var "new_height"))) nil). (* Metode *)

Definition InstantiateRectangle := 
  obj "r" "Rectangle".

Definition ResizeRectangle :=
  methodCall "r" "resize" (cons (num 20) (cons (num 15) nil)).

Inductive MethodCall :=
| call : string -> string -> list AExp -> MethodCall.

