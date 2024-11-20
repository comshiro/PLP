Require Import String.
Require Import Arith.
Definition Env := string -> nat.

Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.


Definition update (env : Env) (var : string) (val : nat) : Env :=
fun x => if (string_dec var x )
          then val
          else (env x ).

Check string_dec.

(*
Fixpoint eval (a: AExp) :
 option nat :=
  match a with
  |num n => Some n
  |div a1 a2=>
    match (eval a1), (eval a2) with
    |Some v1, v2 =>
    if Nat.eqb v2 0 
    then None
    else Some(Nat.div v1 v2)
    |_, _
  end
end.
*)
Print Nat.ltb.
Print Nat.sub.

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Fixpoint Eval (env: Env)(exp: AExp) : option nat :=
  match exp with
  | num n => Some n
  | var x => Some (env x)
  | add e1 e2 =>
    match Eval env e1, Eval env e2 with    
    | Some n1, Some n2 => Some (Nat.add n1 n2)
    | _, _ => None
    end
  | sub e1 e2 =>
    match Eval env e1, Eval env e2 with
    | Some n1, Some n2 =>
      if Nat.ltb n2 n1 
      then Some (Nat.sub n1 n2) 
      else None
    | _, _ => None
    end
  | div e1 e2 =>
      match Eval env e1, Eval env e2 with
      | Some n1, Some n2 =>
          if Nat.eqb n2 0
          then None
          else Some (Nat.div n1 n2)
      | _, _ => None
      end
  end.


Print num.
Check add (num 3) (var "x").
Compute add (num 3) (var "x").

Notation "A +' B" :=
  (add A B)
    (left associativity, at level 50).

Check 2 +' 5.

Check option.
Check option nat.
Print option.
Check (Some 2).
Check None.


Print "/\".
Check Some bool.
Check option bool.

Inductive Exp :=
| val : bool -> Exp
| vari : string -> Exp
| conj : Exp -> Exp -> Exp
| not : Exp -> Exp
| disj : Exp -> Exp -> Exp.

Definition envlogics := string->bool.

Fixpoint Evalb (env : envlogics) (exp: Exp) :option bool:=
match exp with
|val v => Some v 
|vari p => Some (env p)
|disj q p =>
  match Evalb env q, Evalb env p with
   |Some false, Some false => Some false
   |_, _ => Some true
  end
|conj q p =>
  match Evalb env q, Evalb env p with
   |Some true, Some true =>Some false
   |_, _ => Some true
  end
|not p =>
  match Evalb env p with
  |Some true => Some false
  |Some false => Some true
  |None => None
  end 
end.

Definition a := true.
Definition b := true.
Coercion val : bool >-> Exp.
Check conj a b.
Compute conj a b.
Definition x := true.
Definition y := false.
Compute (disj x y).
Compute conj x y.

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.
Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| while : Cond -> Stmt -> Stmt.

Fixpoint EvalCond (env: Env)(c: Cond)  : option bool :=
  match c with
  | base b => Some b
  | bnot c' =>
      match EvalCond env c' with
      | Some v => Some (negb v)
      | None => None
      end
  | beq a1 a2 =>
      match Eval env a1, Eval env a2 with
      | Some n1, Some n2 => Some (Nat.eqb n1 n2)
      | _, _ => None
      end
  | less a1 a2 =>
      match Eval env a1, Eval env a2 with
      | Some n1, Some n2 => Some (Nat.ltb n1 n2)
      | _, _ => None
      end
  | band a1 a2 =>
      match EvalCond env a1, EvalCond env a2 with
      | Some true, Some true => Some true
      | _, _ => Some false
      end
  end.


Fixpoint Exec (env: Env)(s: Stmt): Env :=
  match s with
  | skip => env
  | assign x a =>
    match Eval env a with
    |Some v => update env x v
    |None => env
    end
  | seq s1 s2 => 
  let env' := Exec env s1 in 
      Exec env' s2

      
  end.