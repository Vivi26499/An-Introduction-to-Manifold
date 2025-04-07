#import "../Note.typ": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  toc-title: "Chapter 1 Euclidean Spaces",
)
#set enum(numbering: "(i)")
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
  If $f$ is $C^infinity$ in a neighborhood of $p$ in $RR^n$, the *directional derivative* of $f$ at $p$ in the direction of $v$ is defined as the limit
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
#definition[
  A *relation* on a set $S$ is a subset $R$ of $S times S$. Given $x, y in S$, we write $x tilde y$ if and only if $(x, y) in R$. \
  A relation $R$ is an *equivalence relation* if it satisfies the following properties for all $x, y, z in S$:
  + *Reflexivity:* $x tilde x$,
  + *Symmetry:* If $x tilde y$, then $y tilde x$,
  + *Transitivity:* If $x tilde y$ and $y tilde z$, then $x tilde z$.
]

Consider the set of all pairs $(f, U)$ where $U$ is a neighborhood of $p$ and $f: U arrow.r RR$ is a $C^infinity$ function. 
We say that $(f, U)$ is *equivalent* to $(g, V)$ if there exists a neighborhood $W subset.eq (U inter V)$ such that $f|_W = g|_W$.

#definition[
  The *germ* of $f$ at $p$ is the equivalence class of the pair $(f, U)$. \
  We write $C^infinity_p (RR^n)$, or simply $C^infinity_p$, for the set of all germs of $C^infinity$ functions on $RR^n$ at $p$.
]

#definition[
  An *algebra* over a field $K$ is a vector space $A$ over $K$ with a multiplication map
  $
    mu: A times A arrow.r A,
  $
  usually written $mu(a, b) = a dot b$, that satisfies the following properties for all $a, b, c in A$ and $r in K$:
  + *Associativity:* $(a dot b) dot c = a dot (b dot c)$,
  + *Distributivity:* $a dot (b + c) = a dot b + a dot c$ and $(a + b) dot c = a dot c + b dot c$,
  + *Homogeneity:* $r(a dot b) = (r a) dot b = a dot (r b)$.

  Usually we write the multiplication as simply $a b$ instead of $a dot b$.
]

#definition[
  A map $L: V arrow.r W$ between two vector spaces over the field $K$ is said to be a *linear map* or a *linear operator* if for all $u, v in V$ and $r in K$:
  + $L(u + v) = L(u) + L(v)$,
  + $L(r u) = r L(u)$.

  To emphasize the scalars are in the field $K$, such a map is said to be *$K$-linear*.
]

#definition[
  If $A$ and $A'$ are algebras over a field $K$, an *algebra homomorphism* is a linear map $L: A arrow.r A'$ that preserves the algebra multiplication: $L(a b) = L(a) L(b)$ for all $a, b in A$.
]

The addition and multiplication of functions induce corresponding operations on $C^infinity_p$, making it into an algebra over $RR$.

== Derivations at a Point
For each tangent vector $v in T_p RR^n$, the directional derivative at $p$ gives a map
$
  D_v: C^infinity_p arrow.r RR.
$

#definition[
  A linear map $D: C^infinity_p arrow.r RR$ is called a *derivation* at $p$ or a *point derivation* if it satisfies the Leibniz rule:
  $
    D(f g) = D(f) g(p) + f(p) D(g)
  $
  Denote the set of all derivations at $p$ by $cal(D)_p (RR^n)$, which is a vector space over $RR$.
]

Obviously, the directional derivatives at $p$ are all derivations at $p$, so there is a map
$
  phi.alt: T_p (RR^n) &arrow.r cal(D)_p (RR^n), \
  v &arrow.r.bar D_v = v^i lr((diff)/(diff x^i) |)_p.
$
Since $D_v$ is clearly linear in $v$, $phi.alt$ is a linear map of vector spaces.

#lemma[
  If $D$ is a point-derivation of $C^infinity_p$, then $D(c) = 0$ for any constant function $c$.
]

#proof[
  By $RR$-linearity, $D(c) = c D(1)$. By the Leibniz rule, we have
  $
    D(1) &= D(1 dot 1) \
    &= D(1) dot 1(p) + 1(p) dot D(1) \
    &= 2 D(1),
  $
  which implies that $D(1) = 0$, and therefore $D(c) = c D(1) = c dot 0 = 0$.
]

#lemma[
  The map $phi.alt: T_p (RR^n) arrow.r cal(D)_p (RR^n)$ is an isomorphism of vector spaces.
]

#proof[
  To show that $phi.alt$ is injective, suppose $phi.alt(v) = D_v = 0$ for some $v in T_p (RR^n)$. For the coordinate functions $x^j$, we have
  $
    0 = D_v x^j &= v^i lr((diff x^j)/(diff x^i) |)_p \
    &= v^i delta^j_i \
    &= v^j,
  $
  which implies that $v = 0$. Thus, $phi.alt$ is injective. \
  To show that $phi.alt$ is surjective, let $D in cal(D)_p (RR^n)$ and let $(f, V)$ be a representative of a germ in $C^infinity_p$.
  We may assume $V$ is an open ball, hence star-shaped. From Taylor's theorem with remainder, we have
  $
    f(x) = f(p) + (x^i - p^i) g_i (x), quad g_i (p) = (diff f)/(diff x^i) (p).
  $
  Applying $D$ to both sides, we get
  $
    D(f(x)) &= D[f(p)] + D[(x^i - p^i) g_i (x)] \
    &= (D x^i) g_i (p) + (p^i - p^i) D g_i (x) \
    &= (D x^i) g_i (p) \
    &= (D x^i) (diff f)/(diff x^i) (p),
  $
  which gives $D = D_v$ for $v = angle.l D x^1, dots.c, D x^n angle.r$. Thus, $phi.alt$ is surjective.
]

Under this vector space isomorphism $T_p (RR^n) tilde.eq cal(D)_p (RR^n)$, we can identify tangent vectors with derivations at $p$,
and the standard basis $e_1, dots.c, e_n$ of $T_p (RR^n)$ with the set $lr((diff)/(diff x^1)|)_p, dots.c, lr((diff)/(diff x^n)|)_p$ of partial derivatives,
$
  v &= angle.l v^1, dots.c, v^n angle.r \
  &= v^i e_i \
  &= v^i lr((diff)/(diff x^i) |)_p.
$

== Vector Fields
#definition[
  A *vector field* on an open subset $U subset.eq RR^n$ is a function that assigns to each point $p in U$ a tangent vector $X_p in T_p (RR^n)$.
  Since $T_p (RR^n)$ has basis $lr((diff)/(diff x^i)|)_p$, we can write
  $
    X_p = a^i (p) lr((diff)/(diff x^i)|)_p, quad a^i (p) in RR.
  $
  Omitting $p$, we can write 
  $
    X = a^i lr((diff)/(diff x^i)) quad arrow.l.r quad mat(a^1; dots.v; a^n; delim: "["),
  $
  where $a^i$ are functions on $U$. 
  We say that $X$ is $C^infinity$ on $U$ if all the coefficient functions $a^i$ are $C^infinity$ on $U$. \
  The set of all $C^infinity$ vector fields on $U$ is denoted by $frak(X)(U)$.
]

#definition[
  If $R$ is a commutative ring with identity, a (left) $R$-*module* is an abelian group $A$ with a scalar multiplication
  $
    mu: R times A arrow.r A,
  $
  usually written $mu(r, a) = r a$, such that for all $r, s in R$ and $a, b in A$,
  + *Associativity:* $(r s) a = r(s a)$,
  + *Identity:* $1 a = a$,
  + *Distributivity:* $r(a + b) = r a + r b$ and $(r + s)a = r a + s a$.
]

$frak(X)(U)$ is a module over the ring $C^infinity (U)$ with the multiplication defined pointwise:
$
  (f X)_p = f(p) X_p,
$
for $ f in C^infinity (U), X in frak(X)(U), p in U$.

#definition[
  Let $A$ and $A'$ be $R$-modules. An $R$-*module homomorphism* from $A$ to $A'$ is a map $f: A arrow.r A'$ that preserves 
  both the addition and the scalar multiplication: for all $a, b in A$ and $r in R$,
  + $f(a + b) = f(a) + f(b)$,
  + $f(r a) = r f(a)$.
]

== Vector Fields as Derivations
If $X in frak(X)(U)$ and $f in C^infinity (U)$, we can define a new function $X f$ by
$
  (X f)(p) = X_p f quad "for all" p in U.
$
Writing $X = a^i lr((diff)/(diff x^i))$, we have
$
  (X f)(p) = a^i (p) (diff f)/(diff x^i) (p),
$
or
$
  X f = a^i (diff f)/(diff x^i),
$
which is a $C^infinity$ function on $U$. Thus, a $C^infinity$ vector field $X$ induces an $RR$-linear map
$
  X: C^infinity (U) &arrow.r C^infinity (U), \
  f &arrow.r.bar X f.
$
$X(f g)$ satisfies the Leibniz rule:
$
  X(f g) = (X f) g + f(X g).
$

#definition[
  If $A$ is an algebra over a field $K$, a *derivation* on $A$ is a $K$-linear map $D: A arrow.r A$ that satisfies the Leibniz rule:
  $
    D(a b) = (D a) b + a(D b) quad "for all" a, b in A.
  $
  The set of all derivations on $A$ is closed under addition and scalar multiplication and forms a vector space, denoted by $"Der"(A)$.
]

We therefore have a map
$
  phi: frak(X)(U) &arrow.r "Der"(C^infinity (U)), \
  X &arrow.r.bar (f arrow.r.bar X f),
$
which is an isomorphism of vector spaces, just as the map $phi.alt: T_p (RR^n) arrow.r cal(D)_p (RR^n)$.