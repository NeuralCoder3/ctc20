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

Definition dio_two := dio_sum dio_one dio_one.

Definition f' (p:dio) : 
{ p1 & { p2 & 
  forall phi, eval phi p + 
    eval (fun x => S (phi x)) p2 =
    eval (fun x => S (phi x)) p1
}}.
Proof.
elim: p => [n||p [p1 [p2 IHp]] q [q1 [q2 IHq]]|p [p1 [p2 IHp]] q [q1 [q2 IHq]]].
- exists (dio_var n); exists dio_one.
  move => phi /=;lia.
- exists (dio_two); exists dio_one.
  by move => phi /=.
- exists (dio_sum p1 q1); exists (dio_sum p2 q2).
  move => phi /=.
  rewrite -(IHp phi) -(IHq phi).
  lia.
- exists (dio_sum 
      (dio_prod p1 q1)
      (dio_prod p2 q2));
  exists (dio_sum 
      (dio_prod p1 q2)
      (dio_prod p2 q1)).
  move => phi /=.
  rewrite -(IHp phi) -(IHq phi).
  lia.
Defined.


Definition f (pq:dio*dio) : dio*dio :=
let (p,q) := pq in 
let: existT _ p1 (existT _ p2 _) := f' p in 
let: existT _ q1 (existT _ q2 _) := f' q in 
  (dio_sum p1 q2,dio_sum q1 p2)
.

Theorem H10_SAT_to_H10p_SAT : reduces H10_SAT H10p_SAT.
Proof.
exists f.
rewrite /(H10_SAT) /(H10p_SAT) /f.
move => [] p q.
move :(f' p) (f' q) => [p1 [p2 Hp]] [q1 [q2 Hq]] /=.
constructor.
- move => [phi H]. exists phi.
  rewrite -(Hp phi) -(Hq phi) H.
  lia.
- move => [phi H]. exists phi.
  move: H.
  rewrite -(Hp phi) -(Hq phi).
  lia.
Qed.