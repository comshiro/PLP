Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.

Inductive AExp :=
| num : nat -> AExp
| var : string -> string -> AExp  (*object, variable, value *)
| add: AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div: AExp -> AExp -> AExp.

Inductive BExp :=
| btrue : BExp                      
| bfalse : BExp                     
| bnot : BExp -> BExp             
| band : BExp -> BExp -> BExp 
| bor :BExp -> BExp -> BExp 
| beq : AExp -> AExp -> BExp 
| blessthan : AExp -> AExp -> BExp 
| bgreaterthan : AExp -> AExp -> BExp. 

Inductive Stmt :=
| skip : Stmt                           
| assign : string -> string ->  AExp -> Stmt          
| seq : Stmt -> Stmt -> Stmt            
| ite : BExp -> Stmt -> Stmt -> Stmt 
| while : BExp -> Stmt -> Stmt            
| methodCall : string -> string -> list AExp -> Stmt
| constructor : string -> list (string * AExp) -> list(string ->string->Stmt) -> Stmt
| getter : string -> string -> Stmt 
| setter : string -> string -> Stmt. 

Definition to_cons_list (l : list AExp) : list AExp := fold_right cons nil l.

Definition KeyPair := (list(string*string)).
Definition Env := list (KeyPair  * nat). 
Definition EnvMethods := list (KeyPair * (list string) * Stmt).  
(* (ObjectName, ParameterNames, MethodBody) *)

Inductive AccessModifier := 
| public : AccessModifier
| private : AccessModifier
| protected : AccessModifier.

Inductive MemberType :=
| instance : MemberType
| static : MemberType.


Inductive InterfaceDecl :=
  | interface : string -> list (string * list AExp) -> InterfaceDecl.



Inductive ClassDecl :=
  | class : string -> (* Class name *)
            option string -> (* Parent class name *)
            option (list (string * MemberType * AccessModifier * AExp)) ->
            option(list (string * AccessModifier * AExp)) -> (* Attributes *)
            option(list (string * AccessModifier * Stmt)) -> (* Methods *)
            option(list (string * MemberType * AccessModifier * Stmt)) -> (* Methods *)            
            option(list (string * bool * bool)) -> (* Getters/Setters: (attribute_name, generate_getter, generate_setter) *)            
            ClassDecl.

(*  clasa
    nume clasa
    nume clasa parinte
    membru + membertype+ acces_modifier + aexp
    membru + access_modifier + aexp
    membru + access_modifier + stmt
    membru + membertype + accessmodifier + stmt
    var setter getter
*)
Definition EnvClasses := list (string * ClassDecl). (* (ClassName, ClassDefinition) *)

Fixpoint lookup (env : Env) (obj : string) (var : string) : option nat :=
  match env with
  | [] => None
  | ((key, n) :: rest) =>
      if List.existsb (fun p => andb (String.eqb (fst p) obj) (String.eqb (snd p) var)) key
      then Some n
      else lookup rest obj var
  end.

Fixpoint lookup_method (env_methods : EnvMethods) (obj : string) (method_name : string) 
         : option (list string * Stmt) :=
  match env_methods with
  | [] => None
  | ((key, params, body) :: rest) =>
      if andb (String.eqb obj (fst (hd ("", "") key))) 
              (String.eqb method_name (snd (hd ("", "") key))) 
      then Some (params, body)
      else lookup_method rest obj method_name
  end.

Fixpoint update (env : Env) (obj : string) (var : string) (new_val : nat) : Env :=
  match env with
  | [] => [ ([(obj, var)], new_val)]
  | ((key, n) :: rest) =>
      if andb (String.eqb obj (fst (hd ("", "") key))) (* Check obj *)
               (String.eqb var (snd (hd ("", "") key))) (* Check var *)
      then
        (* If found, update the value *)
        ((key, new_val)) :: rest
      else
        (* If not found, continue searching *)
        (key, n) :: (update rest obj var new_val)
  end.

Definition env0 : Env :=
[([("obj1", "x")],10);
([("obj1", "y")],10);
([("obj2", "x")],11)].

Eval compute in lookup env0 "obj1" "x".  (* Should return Some 10 *)
Eval compute in lookup env0 "obj2" "x".  (* Should return Some 20 *)
Eval compute in lookup env0 "obj1" "z".  (* Should return None, because "z" is not found in obj1 *)

Reserved Notation "E =[ S ]=> N" (at level 60).
Inductive aexp_eval : AExp -> Env -> nat -> Prop :=
  | bs_const : forall n sigma, 
      (num n) =[ sigma ]=> n
      
  | bs_var : forall obj x sigma n,
    lookup sigma obj x = Some n -> 
    (var obj x) =[ sigma ]=> n
  
  | bs_add : forall e1 e2 sigma n1 n2,
      e1 =[ sigma ]=> n1 ->
      e2 =[ sigma ]=> n2 ->
      (add e1 e2) =[ sigma ]=> (n1 + n2)
      
  | bs_sub : forall e1 e2 sigma n1 n2,
      e1 =[ sigma ]=> n1 ->
      e2 =[ sigma ]=> n2 ->
      (sub e1 e2) =[ sigma ]=> (n1 - n2)
      
  | bs_mul : forall e1 e2 sigma n1 n2,
      e1 =[ sigma ]=> n1 ->
      e2 =[ sigma ]=> n2 ->
      (mul e1 e2) =[ sigma ]=> (n1 * n2)
      
  | bs_div : forall e1 e2 sigma n1 n2,
      e1 =[ sigma ]=> n1 ->
      e2 =[ sigma ]=> n2 ->
      n2 <> 0 ->
      (div e1 e2) =[ sigma ]=> (Nat.div n1 n2)
where "E =[ S ]=> N" := (aexp_eval E S N).

Reserved Notation "B ={ S }=> b" (at level 70).
Inductive bexp_eval : BExp -> Env -> bool -> Prop :=
  | bs_true : forall sigma,
      btrue ={ sigma }=> true
      
  | bs_false : forall sigma,
      bfalse ={ sigma }=> false
      
  | bs_not : forall b sigma v,
      b ={ sigma }=> v ->
      (bnot b) ={ sigma }=> (negb v)
      
  | bs_and : forall b1 b2 sigma v1 v2,
      b1 ={ sigma }=> v1 ->
      b2 ={ sigma }=> v2 ->
      (band b1 b2) ={ sigma }=> (andb v1 v2)

  | bs_or : forall b1 b2 sigma v1 v2,
      b1 ={ sigma }=> v1 ->
      b2 ={ sigma }=> v2 ->
      (bor b1 b2) ={ sigma }=> (orb v1 v2)
      
  | bs_less : forall a1 a2 sigma n1 n2,
      a1 =[ sigma ]=> n1 ->
      a2 =[ sigma ]=> n2 ->
      (blessthan a1 a2) ={ sigma }=> (Nat.ltb n1 n2)
      
  | bs_greater : forall a1 a2 sigma n1 n2,
      a1 =[ sigma ]=> n1 ->
      a2 =[ sigma ]=> n2 ->
      (bgreaterthan a1 a2) ={ sigma }=> (Nat.ltb n2 n1)
where "B ={ S }=> b" := (bexp_eval B S b).


Definition GradesClass := 
  class "Grades" None (* No parent class *)
    (Some [("PLP", instance, public, num 0); ("AG", instance, public, num 0)]) 
    None (* No static attributes *)
    (Some[("Update", public, seq 
                (assign "this" "PLP" (var "this" "new_PLP"))
                (assign "this" "AG" (var "this" "new_AG")))] )
    None. (* No static methods *)

Inductive Obj :=
| object : string -> string -> Obj.

Definition InstantiateGrade :=
  object "g" "Grade".

Definition UpdateGrade :=
  methodCall "g" "update" (cons (num 5) (cons (num 10) nil)).
                                                                                                                        
Definition RectangleClass := 
  class "Rectangle" (Some "Shape")
    (Some [("length", static, public, num 0); ("width", static, public, num 0)]) 
    None
    (Some[("Resize", public, seq 
                (assign "this" "length" (var "this" "new_length"))
                (assign "this" "width" (var "this" "new_width")))] )
    None.

Definition InstantiateRectangle := 
  object "r" "Rectangle".

Definition ResizeRectangle :=
  methodCall "r" "resize" (cons (num 20) (cons (num 15) nil)).

Inductive MethodCall :=
| call : string -> string -> list AExp -> MethodCall.

Definition PointConstructor :=
  constructor "Point" [("x", num 5); ("y", num 10)].

Definition IndexClass :=
  class "Index" None
    (Some [("count", static, public, num 0)])  (* Static attribute 'count' initialized to 0 *)
    None   (* No instance attributes *)
    None   (* No instance methods *)
    (Some [("increment", static, public,
            assign "Index" "count" (add (var "Index" "count") (num 1)))] )  (* Static method 'increment' to increase 'count' by 1 *)
    None.  (* No static methods *)

Definition PointWithEncapsulationClass :=
  class "Point" None None
    (Some [("x", private, num 0);  
           ("y", private, num 0)])  
    (Some [("getX", public, seq 
                (assign "this" "x" (var "this" "x"))  
                skip);
           ("setX", public, 
                assign "this" "x" (var "this" "new_value"))]) 
    None 
    (Some [("x", true, true); 
           ("y", true, true)]).


Fixpoint stmt_eval (s: Stmt) (sigma: Env) : Env :=
  match s with
  | skip => sigma
  | assign obj variable a =>
      let n := aexp_eval a sigma in
      update sigma obj variable n
  | seq s1 s2 => stmt_eval s2 (stmt_eval s1 sigma)
  | ite b s1 s2 =>
      if bexp_eval b sigma then stmt_eval s1 sigma else stmt_eval s2 sigma
  | while b s =>
      if bexp_eval b sigma then stmt_eval (seq s (while b s)) sigma else sigma
  | methodCall obj method args =>
      match lookup_method EnvMethods obj method with
      | None => sigma
      | Some (params, body) =>
          if (length params =? length args)%nat then
            let arg_vals := map (fun a => aexp_eval a sigma) args in
            let method_env := fold_left 
              (fun env_acc '(param_name, val) => 
                update env_acc obj param_name val)
              (combine params arg_vals)
              sigma in
            stmt_eval body method_env
          else sigma
      end
  | constructor class_name init_list constructor_stmts =>
      let init_env := fold_left 
        (fun env_acc '(attr_name, init_expr) => 
          let init_val := aexp_eval init_expr sigma in
          update env_acc class_name attr_name init_val)
        init_list
        sigma in
      fold_left 
        (fun env_acc stmt => 
          stmt_eval (stmt class_name "this") env_acc)
        constructor_stmts 
        init_env
  | getter obj attr =>
      match lookup sigma obj attr with
      | None => sigma
      | Some v => update sigma "this" "result" v
      end
  | setter obj attr =>
      match lookup sigma "this" "new_value" with
      | None => sigma
      | Some new_val => update sigma obj attr new_val
      end
  end.




