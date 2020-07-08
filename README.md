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

We construct f' using the following rules:
<img src="https://render.githubusercontent.com/render/math?math=(%5Cexists%20%5Cvarphi.p%5B%5Cvarphi%5D%3Dq%5B%5Cvarphi%5D)%5Cleftrightarrow%20%5Cexists%20%5Cvarphi.%20p_1%5B1%2B%5Cvarphi%5D%2Bq_2%5B1%2B%5Cvarphi%5D%3Dq_1%5B1%2B%5Cvarphi%5D%2Bp_2%5B1%2B%5Cvarphi%5D">
<!-- \begin{align*}
x &\mapsto (x,1) \approx x-1 \\
1 &\mapsto (1+1,1) \approx 2-1=1 \\
p+q &\mapsto (p_1+q_1,p_2+q2) \approx (p_1-p_2)+(q_1-q_2) \\
p\cdot q &\mapsto (p_1\cdot q_1+p_2\cdot q_2,p_1\cdot q_2+p_2\cdot q_1) \approx (p_1-p_2)\cdot(q_1-q_2)
\end{align*} -->

## Reduction proof


In the reduction proof, one has to show that the transformed equation is positive satisfiable if and only if the original equation is satisfiable.
The proof will be stronger, as we will show that the evaluation can be kept.
<!-- (\exists \varphi.p[\varphi]=q[\varphi])\leftrightarrow \exists \varphi. p1[1+\varphi]+q2[1+\varphi]=q1[1+\varphi]+p2[1+\varphi] -->
<img src="https://render.githubusercontent.com/render/math?math=(%5Cexists%20%5Cvarphi.p%5B%5Cvarphi%5D%3Dq%5B%5Cvarphi%5D)%5Cleftrightarrow%20%5Cexists%20%5Cvarphi.%20p1%5B1%2B%5Cvarphi%5D%2Bq2%5B1%2B%5Cvarphi%5D%3Dq1%5B1%2B%5Cvarphi%5D%2Bp2%5B1%2B%5Cvarphi%5D">

We use the assumptions provided by the specification of the transformation:
<!-- \begin{align*}
\forall \varphi.~p[\varphi]+p2[1+\varphi] = p1[1+\varphi] \\
\forall \varphi.~q[\varphi]+q2[1+\varphi] = q1[1+\varphi]
\end{align*} -->
<img src="https://render.githubusercontent.com/render/math?math=%5Cbegin%7Balign*%7D%0A%5Cforall%20%5Cvarphi.%20p%5B%5Cvarphi%5D%2Bp_2%5B1%2B%5Cvarphi%5D%20%26%3D%20p_1%5B1%2B%5Cvarphi%5D%20%5C%5C%0A%5Cforall%20%5Cvarphi.%20q%5B%5Cvarphi%5D%2Bq_2%5B1%2B%5Cvarphi%5D%20%26%3D%20q_1%5B1%2B%5Cvarphi%5D%0A%5Cend%7Balign*%7D%0A">

The first direction from left to right is easy, as one can rewrite p1 and q1 with the two assumptions from right to left.
With the assumption that p and q are equal under the evaluation, the goal is solvable by commutativity of addition.

For the second direction from right to left, one can rewrite p1 and q1 with the two assumptions in the right hand side. By injectivity of addition, the proof is finished.
