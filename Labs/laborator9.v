Require Import String.

Inductive E : Type :=
| O : E                                
| S : E -> E                        
| isZero : E -> E                   
| T : E
| F : E
| ite : E -> E -> E -> E.      

Definition Env := string -> E.
Definition empty_env : Env := fun _ => O.  
Definition update (sigma : Env) (x : string) (v : E) : Env :=
  fun y => if String.eqb x y then v else sigma y.

Inductive e_eval : E -> E -> Prop :=
| eval_isZeroO : e_eval (isZero O) T
| eval_isZeroS : forall e, e_eval (isZero (S e)) F
| eval_iteT : forall e1 e2, e_eval (ite T e1 e2) e1
| eval_iteF : forall e1 e2, e_eval (ite F e1 e2) e2
| eval_iteStep : forall e1 e1' e2 e3,
    e_eval e1 e1' -> e_eval (ite e1 e2 e3) (ite e1' e2 e3)
| eval_Step : forall e e',
    e_eval e e' -> e_eval (S e) (S e')
| eval_isZeroStep : forall e e',
    e_eval e e' -> e_eval (isZero e) (isZero e').



Inductive e_closure : E -> E -> Prop :=
| closure_refl : forall e, e_closure e e
| closure_step : forall e1 e2 e3,
    e_eval e1 e2 -> e_closure e2 e3 -> e_closure e1 e3.


Example test_eval : e_closure (isZero O) T.
Proof.
  apply closure_step with (e2 := T).
  - apply eval_isZeroO.
  - apply closure_refl.
Qed.

Example test_eval_isZero_O : e_closure (isZero O) T.
Proof.
  apply closure_step with (e2 := T).
  - apply eval_isZeroO.
  - apply closure_refl.
Qed.

Example test_eval_ite_T : e_closure (ite T (S O) (S (S O))) (S O).
Proof.
  apply closure_step with (e2 := (S O)).
  - apply eval_iteT.
  - apply closure_refl.
Qed.

Example test_eval_isZero_S_O : e_closure (isZero (S O)) F.
Proof.
  apply closure_step with (e2 := F).
    apply eval_isZeroS.
    apply closure_refl.
Qed.


(*

           .
TZero ------------
        O : Nat

         e : Nat
TSucc -------------
        S e : Nat

          e : Nat
 TIsZero -----------
         isZero e : bool
          .
TT ------------
        T : bool
          .
TF ------------
        F : bool

      e1 : bool    e2 : Nat    e3 : Nat
TIte  -----------------------
      ite e1 e2 e3 : Nat

*)
Inductive type : E -> Type :=
  | TZero : type O
  | TSucc : forall e, type e -> type (S e)
  | TIsZero : forall e, type e -> type (isZero e)
  | TT : type T
  | TF : type F
  | TIte : forall e1 e2 e3, type e1 -> type e2 -> type e3 -> type (ite e1 e2 e3).

(*
      .
 ------------ TZero
  O : Nat
 ------------ TSucc
  S O : Nat

*)
Example test_type_succ_O : type (S O).
Proof.
  apply TSucc.
  apply TZero. 
Qed.

(*
                                          
 -------   TT  ------------------ TSucc   ------------------------TSucc
   T: bool         S O : Nat            S (S O) : Nat

------------------------------------------------------ TIte
ite T (S O) (S (S O)) : Nat


*)
Example test_type_ite : type (ite T (S O) (S (S O))).
Proof.
  apply TIte.
  - apply TT.
  - apply TSucc. apply TZero. 
  - apply TSucc. apply TSucc. apply TZero.
Qed.


(*

    -------
      O: Nat
    --------------TSucc
      S O : Nat
    -----------------------TIsZero
      isZero (S O) : Bool


*)
Example test_type_isZero_S_O : type (isZero (S O)).
Proof.
  apply TIsZero. 
  apply TSucc. apply TZero. 
Qed.
