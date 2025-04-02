#import "../Note.typ": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  toc-title: "Table of Contents",
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
  The set of all $C^infinity$ functions on $U$ is denoted by $C^infinity(U)$ or $cal(F)(U)$.
]
The function $f: U arrow.r RR$ is real-analytic at $p$ if in some neighborhood of $p$, it is equal to its Taylor series at $p$. \
A real-analytic function is necessarily $C^infinity$, but the converse is not true. 

== Taylor's Theorem with Remainder
#definition[
  A subset $S subset.eq RR^n$ is *star-shaped* with respect to a point $p in S$ if for every point $x in S$, the line segment from $p$ to $x$ lies entirely in $S$. \

]