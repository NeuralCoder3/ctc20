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

From Coq Require Import Lia.
From Coq Require Import ssreflect ssrfun ssrbool.

Notation " g ∘ f " := (fun x => g (f x)) (at level 40, left associativity).

(* multivariate Diophantine polynomial *)
Inductive dio : Set :=
  | dio_var : nat -> dio (* variable *)
  | dio_one : dio (* constant 1 *)
  | dio_sum : dio -> dio -> dio (* sum *)
  | dio_prod : dio -> dio -> dio. (* product *)

Notation "` n" := (dio_var n) (at level 30).
Infix "`+" := dio_sum (at level 60).
Infix "`*" := dio_prod (at level 55).
Notation "`1" := dio_one.
Notation "`2" := (dio_sum dio_one dio_one).

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
(* 
  For all formulas p that evaluate to some n with the valuation ϕ,
  we can get an equivalent formula q-r that evaluates to n with the
  valuation S∘ϕ.

      E ϕ p = E (S∘ϕ) (q - r)
            = E (S∘ϕ) q - E (S∘ϕ) r

  to stay positive we reformulate this as

      E ϕ p + E (S∘ϕ) r = E (S∘ϕ) q
*)
Definition translate (p : dio) : { '(q, r) |
  forall ϕ, eval ϕ p + eval (S ∘ ϕ) r = eval (S ∘ ϕ) q }.
Proof.
  elim: p => [ x
             |
             | p1 [[q1 r1] IH1] p2 [[q2 r2] IH2]
             | p1 [[q1 r1] IH1] p2 [[q2 r2] IH2] ].
  - exists (`x, `1)=> /=. lia.
  - exists (`2, `1)=> /=. lia.
  - exists ((q1 `+ q2) , (r1 `+ r2))=> > /=. rewrite -(IH1 _) -(IH2 _) ; lia.
  - exists ((q1 `* q2 `+ r1 `* r2) , (q1 `* r2 `+ r1 `* q2)) => > /=. rewrite -(IH1 _) -(IH2 _) ; lia.
Defined.
    
(*
  For all p₁, p₂ we have some q₁,r₁,q₂,r₂ such that:

      E ϕ p₁ = E (S∘ϕ) q₁ - E (S∘ϕ) r₁
      E ϕ q₁ = E (S∘ϕ) q₂ - E (S∘ϕ) r₂

  From this we get the reduction:
  
         E ϕ p₁                  = E ϕ q₁
      ⇔  E (S∘ϕ) q₁ - E (S∘ϕ) r₁ = E (S∘ϕ) q₂ - E (S∘ϕ) r₂
      ⇔  E (S∘ϕ) q₁ + E (S∘ϕ) r₂ = E (S∘ϕ) q₂ + E (S∘ϕ) r₁
*)
Definition reduction (p1p2 : dio * dio) : dio * dio :=
  let (p1 , p2) := p1p2 in
  let (q1 , r1) := proj1_sig (translate p1) in
  let (q2 , r2) := proj1_sig (translate p2) in
  ((q1 `+ r2) , (q2 `+ r1)).

Theorem H10_SAT_to_H10p_SAT : reduces H10_SAT H10p_SAT.
Proof.
  exists reduction => [[p1 p2]].
  rewrite /reduction.
  move: (translate p1) (translate p2) => [[q1 r1] H1] [[q2 r2] H2] /=.
  split=> [[ϕ]|[ϕ]].
  - exists ϕ. rewrite -(H1 _) -(H2 _). lia.
  - rewrite -(H1 _) -(H2 _). exists ϕ. lia.
Qed.
