#import "../Note.typ": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  toc-title: "Chapter 1 Euclidean Spaces",
)

= Smooth Functions on a Euclidean Space
The calculus of $C^infinity$ functions will be our primary tool for studying higher-dimensional manifolds.

== $C^infinity$ Analytic Functions
Let $p = (p^1, dots.c, p^n)$ be a point in an open subset $U subset RR^n$.
#definition[
  Let $k$ be a non-negative integer. A real-valued function $f: U arrow.r RR$ is said to be $C^k$ at $p$ if its partial derivatives
  $ 
    (diff^j f)/(diff x_1^(i_1) dots.c diff x_n^(i_n))
  $
  of all orders $j lt.eq k$ exist and are continuous at $p$. \
  The function $f: U arrow.r RR$ is $C^infinity$ at $p$ if it is $C^k$ at $p$ for all $k gt.eq 0$. \
  A vector-valued function $f: U arrow.r RR^m$ is said to be $C^k$ at $p$ if all of its components $f^1, dots.c, f^m$ are $C^k$ at $p$. \
  $f: U arrow.r RR$ is said to be $C^k$ on $U$ if it is $C^k$ at every point $p in U$. \
  The set of all $C^infinity$ functions on $U$ is denoted by $C^infinity (U)$ or $cal(F)(U)$.
]
The function $f: U arrow.r RR$ is real-analytic at $p$ if in some neighborhood of $p$, it is equal to its Taylor series at $p$. \
A real-analytic function is necessarily $C^infinity$, but the converse is not true. 

== Taylor's Theorem with Remainder
#definition[
  A subset $S subset.eq RR^n$ is *star-shaped* with respect to a point $p in S$ if for every point $x in S$, the line segment from $p$ to $x$ lies entirely in $S$. 
]
#lemma[
  Let $f in C^infinity (U)$, where $U subset RR^n$ is an open subset, star-shaped with respect to a point $p in U$. Then there are functions $g_1 (x), dots.c, g_n (x) in C^infinity (U)$ such that
  $ 
    f(x) = f(p) + (x^i - p^i) g_i (x), quad g_i (x) = (diff f)/(diff x^i) (p).
  $
]
If $f$ is a $C^infinity$ function on an open subset $U$ containing $p$, then there is an $epsilon > 0$ such that
$
  p in B(p, epsilon) subset U,
$
where $B(p, epsilon) = { x in RR^n : ||x - p|| < epsilon }$ is the open ball of radius $epsilon$ centered at $p$, which is clearly star-shaped with respect to $p$.

= Tangent Vevtors in $RR^n$ as Derivations
In this section, we will find a characterization of tangent vectors in $RR^n$ that will generalize to manifolds. 

== The Directional Derivative
To distinguish between points and vectors, we write a point in $RR^n$ as $p = (p^1, dots.c, p^n)$ and a vector in
the tangent space at $p$, denoted by $T_p RR^n$, as
$
  v = mat(v^1; dots.v; v^n; delim: "[") "or" v = angle.l v^1, dots.c, v^n angle.r. 
$
We usually denote the standard basis of $RR^n$ by $e_1, dots.c, e_n$, then $v = v^i e_i$ for some $v^i in RR$.\
The line through $p = (p^1, dots.c, p^n)$ in the direction of $v = (v^1, dots.c, v^n)$ has parametrization
$
  c(t) = (p^1 + t v^1, dots.c, p^n + t v^n).
$
#definition[
  If $f$ is $C^infinity$ in a neighborhood of $p$ in $RR^n$, the *directional derivative* of $f$ at $p$ in the direction of $v$ is defined as the limit $ {lr(1/2x^2|)^(x=n)_(x=0) + (2x+3)} $
  $
    D_v f &= lim_(t arrow.r 0) (f(c(t)) - f(c(0))) / t \
    &= lr(dif/(dif t)|)_(t=0) f(c(t)) \
    &= (dif c^i) / (dif t) (0) (diff f) /(diff x^i) (p) \
    &= v^i (diff f) /(diff x^i) (p).
  $
  We write
  $
    D_v = v^i lr(diff/(diff x^i)|)_p
  $
  for the map from a function $f$ to its directional derivative $D_v f$.
]
The association $v arrow.r D_v$ offers a way to characterize tangent vectors as a certain operators on $C^infinity$ functions.

== Germs of Functions