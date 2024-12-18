Require Import String.
Require Import List.
Open Scope string_scope.
Import ListNotations.

(* expressions *)
Inductive Exp :=
| var : string -> Exp
| val : nat -> Exp
| plus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp.

Coercion var : string >-> Exp.
Coercion val : nat >-> Exp.
Notation "A +' B" := (plus A B) (left associativity, at level 50).
Notation "A *' B" := (times A B) (left associativity, at level 40).

Check "n" +' 10 *' "y".

(* interpreter *)
Fixpoint interpret
  (e : Exp)
  (sigma : string -> nat) : nat :=
  match e with
  | val n => n
  | var x => sigma x
  | plus e1 e2 => (interpret e1 sigma)
                  + (interpret e2 sigma)
  | times e1 e2 => (interpret e1 sigma)
                  * (interpret e2 sigma)
  end.

Definition env1 :=
  fun y => if y =? "n"
           then 11
           else 0.

Compute interpret
  ("n" +' 10 *' "y")
  env1.

Compute interpret
  ("n" +' 10 *' 2)
  env1.


(* stack machine *)
Inductive Instruction :=
| push_const : nat -> Instruction
| push_var : string -> Instruction
| add : Instruction
| mul : Instruction.

Definition run_instruction
  (i : Instruction)
  (env : string -> nat)
  (stack : list nat) :=
  match i with
  | push_const n => n :: stack
  | push_var x => (env x) :: stack
  | add => match stack with
           | n1 :: n2 :: rest =>
               (n1 + n2) :: rest
           | _ => stack
           end
  | mul => match stack with
           | n1 :: n2 :: rest =>
               (n1 * n2) :: rest
           | _ => stack
           end
  end.


Compute run_instruction add env1 [2;3].
Compute run_instruction add env1 [2;3;6;5].
Compute run_instruction
  (push_var "n")
  env1
  [].

Fixpoint run_instructions
  (is' : list Instruction)
  (env : string -> nat)
  (stack : list nat) :=
  match is' with
  | nil => stack
  | i :: is'' =>
      run_instructions is'' env
        (run_instruction i env stack)
  end.

Compute run_instructions
  [push_const 3; push_var "n"; mul]
  env1
  [].

(* compiler *)
(* Exp --> [Instruction] *)
Fixpoint compile
  (e : Exp) : list Instruction :=
  match e with
  | val n => [push_const n]
  | var x => [push_var x]
  | plus e1 e2 =>
      (compile e2) ++ (compile e1) ++ [add]
  | times e1 e2 =>
      (compile e2) ++ (compile e1) ++ [mul]
  end.
  

Compute compile ("n" +' 5).
Compute compile (("n" +' 5) *' 10).
Compute compile ("n" +' 5 *' 10).

Compute interpret ("n" +' 5) env1.
Compute run_instructions
  (compile ("n" +' 5))
  env1
  [].

(* compilation soundness *)
Lemma compilation_helper:
  forall e is' env stack,
    run_instructions (compile e ++ is') env stack =
      run_instructions is' env (interpret e env :: stack).
Proof.
  induction e; intros is' env stack.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite <- app_assoc.
    rewrite IHe1.
    simpl.
    reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite <- app_assoc.
    rewrite IHe1.
    simpl.
    reflexivity.
Qed.                         
                   
Theorem compilation_sound:
  forall e env,
    run_instructions (compile e) env [] =
      [interpret e env].
Proof.
  intros.
  Print List.
  rewrite <- app_nil_r with (l := compile e).
  rewrite compilation_helper.
  simpl.
  reflexivity.
Qed.
```