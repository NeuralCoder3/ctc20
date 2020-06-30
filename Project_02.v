(*
  Project 2: H10_SAT_to_H10p_SAT
    Many-one reduction from 
	Diophantine Equation Solvability to
  Positive Diophantine Equation Solvability

  Constructive Theory of Computation
  Summer Semester 2020
  Saarland University

  Assignees:
    Ullrich, Marcel
    Patzek, Jaqueline
    Spaniol, Daniel
    (Dutra, Rafael)
*)

(* multivariate Diophantine polynomial *)
Inductive dio : Set :=
  | dio_var : nat -> dio (* variable *)
  | dio_one : dio (* constant 1 *)
  | dio_sum : dio -> dio -> dio (* sum *)
  | dio_prod : dio -> dio -> dio. (* product *)

(* Diophantine polynomial evaluation wrt. φ *)
Fixpoint eval (φ: nat -> nat) (p: dio) : nat :=
  match p with
  | dio_var x => φ x
  | dio_one => 1
  | dio_sum q r => eval φ q + eval φ r
  | dio_prod q r => eval φ q * eval φ r
  end.

(* Diophantine Equation Solvability *)
Definition H10_SAT : (dio * dio) -> Prop :=
  fun '(p, q) => exists (φ: nat -> nat), eval φ p = eval φ q.

(* Positive Diophantine Equation Solvability *)
Definition H10p_SAT : (dio * dio) -> Prop :=
  fun '(p, q) => exists (φ: nat -> nat), eval (fun x => 1 + φ x) p = eval (fun x => 1 + φ x) q.

(* many-one reduction *)
Definition reduces {X Y} (p : X -> Prop) (q : Y -> Prop) := exists f : X -> Y, forall x, p x <-> q (f x).



(* demonstration of useful techniques *)

Require Import Lia.
Require Import ssreflect ssrfun ssrbool.



Theorem H10_SAT_to_H10p_SAT : reduces H10_SAT H10p_SAT.
Proof.
Admitted.