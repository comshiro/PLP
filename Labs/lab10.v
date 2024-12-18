Require Import String.
Require Import List.
Import ListNotations.

Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.

Fixpoint interpret (b : B) : bool :=
  match b with
  | T => true
  | F => false
  | neg b1 => negb (interpret b1)
  | and b1 b2 => andb (interpret b1) (interpret b2)
  | or b1 b2 => orb (interpret b1) (interpret b2)
  end.

Inductive Instruction :=
| push : nat -> Instruction
| inv : Instruction
| add : Instruction
| mul : Instruction.

Definition run_instruction (i : Instruction) (stack : list nat) : list nat :=
  match i with
  | push n => match n with
              | O => O :: stack
              | S n' => (S O) :: stack
              end
  | inv => match stack with
           | O :: rest => (S O) :: rest
           | (S O) :: rest => O :: rest
           | _ => stack
           end
| add => match stack with
         | (S O) :: _ :: rest => (S O) :: rest 
         | _ ::(S O) :: rest => (S O) :: rest
         | O :: O:: rest => O :: rest
         | _ => stack
         end
| mul => match stack with
         | O :: _ :: rest => O :: rest 
         | _ :: O :: rest => O :: rest
         | (S O) :: (S O) :: rest => (S O) :: rest
         | _ => stack
         end
  end.

Fixpoint run_instructions
  (stpgm : list Instruction)
  (stack : list nat) :=
  match stpgm with
  | nil => stack
  | i :: stpgm' =>
      run_instructions stpgm'
        (run_instruction i stack)
  end.

Fixpoint compile (b : B) : list Instruction :=
  match b with
  | T => [push 1]
  | F => [push 0]
  | neg b1 => compile b1 ++ [inv]
  | and b1 b2 => compile b1 ++ compile b2 ++ [mul]
  | or b1 b2 => compile b1 ++ compile b2 ++ [add]
  end.

Definition to_nat (b : bool) : nat :=
  if b then 1 else 0.

Lemma soundness_helper:
  forall b instrs stack,
    run_instructions ((compile b) ++ instrs) stack =
    run_instructions instrs (to_nat (interpret b) :: stack).
Proof.
induction b; intros.
-reflexivity.
-reflexivity.
- simpl.
    rewrite <- app_assoc.
    rewrite IHb.
    destruct (interpret b).
    --reflexivity.
    --reflexivity.
-simpl.
    rewrite <- app_assoc.
    rewrite IHb1.
    rewrite <- app_assoc.
    rewrite IHb2.
    simpl.
    destruct (interpret b1).
    destruct (interpret b2).
    reflexivity.
    destruct (interpret b1); destruct (interpret b2); reflexivity.
    destruct (interpret b1); destruct (interpret b2); reflexivity.
-simpl.
    rewrite <- app_assoc.
    rewrite IHb1.
    rewrite <- app_assoc.
    rewrite IHb2.
    destruct (interpret b1).
    destruct (interpret b2).
    reflexivity.
    destruct (interpret b1); destruct (interpret b2); reflexivity.
    destruct (interpret b1); destruct (interpret b2); reflexivity.
Qed.

Theorem soundness:
  forall b,
    run_instructions (compile b) nil = [to_nat (interpret b)].
Proof.
  intros b.
  Print List.
  rewrite <- app_nil_r with (l := compile b).
  rewrite soundness_helper.
  simpl.
  reflexivity.
Qed.


