# Constructive Theory of Computation
## Project 2: Diophantine

Team members: Marcel Ullrich, Jaqueline Patzek, Daniel Spaniol, Rafael Dutra

## Goal

We want to show that the solvability of diophantine equations reduces (by many-one reduction) to positive diophantine equation solvability.
Positive diophantine equations only allow for the evaluation with strictly positive
instantiations of variables.

We define diophantine equations as an inductive type `dio`:
<center>
<img src="https://latex.codecogs.com/svg.latex?p,&space;q:dio::=x~|~1~|~p+q~|~p\cdot&space;q">
</center>

In mathematical notation the goal is:
<center>
<img src="https://latex.codecogs.com/svg.latex?\text{H10}_\text{SAT}\preceq\text{H10p}_\text{SAT}">
</center>

<br>

With a bit of notation and unfolding of the definition for <img src="https://latex.codecogs.com/svg.latex?\text{H10}_\text{SAT}"> and <img src="https://latex.codecogs.com/svg.latex?\text{H10p}_\text{SAT}"> we can reformulate the goal into:

<center>
<img src="https://latex.codecogs.com/svg.latex?\exists&space;(f:dio\times&space;dio\to&space;dio\times&space;dio).~\forall(p:dio,q:dio).\\(\exists\varphi.~p=_\varphi&space;q)\leftrightarrow(\exists\varphi.~\pi_1~(f~p)=_{1+\varphi}\pi_2~(f~q))">
</center>

We use the notation <img src="https://latex.codecogs.com/svg.latex?p=_\varphi&space;q"> to express that p and q evaluate to the same value under the variable assignment defined by  <img src="https://latex.codecogs.com/svg.latex?\varphi">.
Futhermore, we introduce the notation <img src="https://latex.codecogs.com/svg.latex?p[\varphi]"> to evaluate <img src="https://latex.codecogs.com/svg.latex?p"> with <img src="https://latex.codecogs.com/svg.latex?\varphi">.

## Idea

The idea is to use a function <img src="https://latex.codecogs.com/svg.latex?f'"> that manipulates the uses of variables such that  <img src="https://latex.codecogs.com/svg.latex?(f'~p)[\varphi+1]=p[\varphi]"> holds.
Therefore, f' should map x to x-1:
<img src="https://latex.codecogs.com/svg.latex?f'~x\mapsto(x-1)">
This is not directly doable, as we work on natural numbers and subtraction is not possible in our model of diophantine equations.

Instead we can use the fact that one can move subtractions to the right-hand side of the equations:
<img src="https://latex.codecogs.com/svg.latex?p_1-p_2=q\leftrightarrow&space;p_1=q+p_2">

Therefore, the new specification for f' becomes:
<img src="https://latex.codecogs.com/svg.latex?f':\forall(p:dio).~\Sigma_{p_1,p_2}~p[\varphi]+p_2[1+\varphi]=p_1[1+\varphi]">
Mathematically speaking, this specification expresses that f' transforms a diophantine formula p into two formulas p1 and p2 such that p is equal to p1-p2 or, equivalently, p+p2 is equal to p1.

Afterwards f' can be used to build the desired reduction function f:
We know
<center>
<img src="https://latex.codecogs.com/svg.latex?p+p_2=p_1">
<img src="https://latex.codecogs.com/svg.latex?q+q_2=q_1">
</center>
Therefore,
<center>
<img src="https://latex.codecogs.com/svg.latex?p=p_1-p_2">
<img src="https://latex.codecogs.com/svg.latex?q=q_1-q_2">
<img src="https://latex.codecogs.com/svg.latex?p=q\leftrightarrow&space;p_1-p_2=q_1-q_2\leftrightarrow&space;p_1+q_2=q_1+p_2">
</center>

## Function realization
The reduction function f can straightforwardly be implemented using the described transformations:
<center>
<img src="https://latex.codecogs.com/svg.latex?f~(p,q):=(p_1+q_2,q_1+p_2)">
<img src="https://latex.codecogs.com/svg.latex?p=q\mapsto&space;p_1+p_2=q_1+p_2">
</center>

Due to the expressiveness of Coq's dependent type theory, one can directly write the function f' together with the specification.

<span style="color:red">TODO: state rules of f'</span>

## Reduction proof

<span style="color:red">TODO: Explain proof</span>

