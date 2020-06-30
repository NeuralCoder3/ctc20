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

Theorem H10_SAT_to_H10p_SAT : reduces H10_SAT H10p_SAT.
Proof.
Admitted.


(* demonstration of useful techniques *)

Require Import Lia.
Require Import ssreflect ssrfun ssrbool.

(* demonstration of how to represent conjunction of Diophantine equalities *)
Lemma encode_and (p1 q1 p2 q2: dio) : { '(p, q) | 
  forall φ, ((eval φ p1 = eval φ q1 /\ eval φ p2 = eval φ q2)) <-> (eval φ p = eval φ q) }.
Proof.
  exists (
    (dio_sum (dio_prod (dio_sum p1 p2) (dio_sum p1 p2)) p2),
    (dio_sum (dio_prod (dio_sum q1 q2) (dio_sum q1 q2)) q2)).
  move=> φ. constructor.
  - by move=> /= [-> ->].
  - move=> /=.
    move: (eval φ p1) (eval φ p2) (eval φ q1) (eval φ q2) => a1 b1 a2 b2.
    have [|]: a1 + b1 = a2 + b2 \/ a1 + b1 <> a2 + b2 by lia.
    all: by nia.
Qed.

(* demonstration of how to represent disjunction of Diophantine equalities *)
Lemma encode_or (p1 q1 p2 q2: dio) : { '(p, q) | 
  forall φ, ((eval φ p1 = eval φ q1 \/ eval φ p2 = eval φ q2)) <-> (eval φ p = eval φ q) }.
Proof.
  exists (
    (dio_sum (dio_prod p1 p2) (dio_prod q1 q2)),
    (dio_sum (dio_prod p2 q1) (dio_prod p1 q2))).
  move=> φ /=. by nia.
Qed.
