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

= The Exterior Algebra of Multicovectors

== Dual Spaces
#definition[
  If $V$ and $W$ are real vector spaces, we denote by $"Hom"(V, W)$ the vector space of all linear maps $f: V arrow.r W$. \
  The *dual space* $V^or$ of $V$ is the vector space of all the real-valued linear functions on $V$:
  $
    V^or = "Hom"(V, RR).
  $
  The elements of $V^or$ are called *covectors* or *1-covectors* on $V$.
]
In the rest of this section, assume $V$ to be a _finite-dimensional_ vector space. Let $e_1, dots.c, e_n$ be a basis of $V$. Then every $v in V$ is uniquely a linear combination $v = v^i e_i$ with $v^i in RR$. \
Let $alpha^i: V arrow.r RR$ be the linear function that picks out the $i$th coordinate, $alpha^i (v) = v^i$. Note that
$
  alpha^i (e_j) = delta^i_j.
$
#proposition[
  The functions $alpha^1, dots.c, alpha^n$ form a basis of $V^or$.
]
#proof[
  Let $f in V^or$ and $v = v^i e_i in V$, then
  $
    f(v) &= v^i f(e_i) \
    &= f(e_i) alpha^i (v),
  $
  which means $f = f(e_i) alpha^i$, i.e., $alpha^1, dots.c, alpha^n$ span $V^or$. \
  Suppose $c_i alpha^i = 0$ for some $c_i in RR$. Applying both sides to $e_j$ gives
  $
    0 &= c_i alpha^i (e_j) \
    &= c_i delta^i_j \
    &= c_j,
  $
  which means $alpha^1, dots.c, alpha^n$ are linear independent.
]
The basis $alpha^1, dots.c, alpha^n$ of $V^or$ is said to be _dual_ to the basis $e_1, dots.c, e_n$ of $V$.

== Permutations
#definition[
  Fix a positive integer $k$. A *permutation* of a set $A = {1, dots.c, k}$ is a bijection $sigma: A arrow.r A$. $sigma$ can be thought of as a reordering of the list $1, dots.c, k$ from $1, dots.c, k$ to $sigma(1), dots.c, sigma(k)$. \
  A simple way to describe a permutation is by its matrix
  $
    M(sigma) = mat(1, dots.c, k; sigma(1), dots.c, sigma(k) ;delim: "[").
  $
  The *cyclic permutation*, $(a_1 thick dots.c thick a_r)$ where $a_i$ are distinct, is the permutation $sigma$ such that $sigma(a_1) = a_2, dots.c, sigma(a_(r-1)) = a_r, sigma(a_r) = a(1)$ and fixes all other elements of $A$. A cyclic permutation $(a_1, dots.c, a_r)$ is called a *cycle of length $r$* or a *r-cycle*. \
  A *transposition* is a $2$-cycle, i.e., a cycle of the form $(a_1 thick a_2)$ that interchanges $a_1$ and $a_2$ and fixes all other elements of $A$. \
  Two cycles $(a_1 thick dots.c thick a_r)$ and $(b_1 thick dots.c thick b_s)$ are *disjoint* if $a_i eq.not b_j$ for all $i$ and $j$. \
  The *product* $tau sigma$ of two permutations $sigma$ and $tau$ of $A$ is the composition $tau thick circle.small thick sigma$.
]
Any permutation can be written as a product of disjoint cycles $(a_1 thick dots.c thick a_r)(b_1 thick dots.c thick b_s) thick dots.c$.
#definition[
  Let $S_k$ be the set of all permutations of the set ${1, dots.c, k}$. A permutation is *even* or *odd* if it can be expressed as a product of an even or odd number of transpositions, respectively. \
  The *sign* of a permutation $sigma in S_k$ is defined as
  $
    "sgn"(sigma) = cases(
      1"," &"if" sigma "is even",
      -1"," &"if" sigma "is odd".
    )
  $
  Clearly, $"sgn"(sigma tau) = "sgn"(sigma) "sgn"(tau)$ for all $sigma, tau in S_k$.
]
Generally, the $r$-cycle can be decomposed into $r-1$ transpositions:
$
  (a_1 thick dots.c thick a_r) = (a_1 thick a_r)(a_1 thick a_(r-1)) thick dots.c thick (a_1 thick a_2),
$
which means that an $r$-cycle is even if $r$ is odd and odd if $r$ is even. Thus one way to compute the sign of a permutation is to decompose it into a product of disjoint cycles and count the number of even-length cycles. \
#definition[
  An *inversion* of a permutation $sigma$ is an ordered pair $(sigma(i), sigma(j))$ such that $i lt j$ but $sigma(i) gt sigma(j)$. 
]
The second way to compute the sign of a permutation is to count the number of inversions. \
#proposition[
  A permutation $sigma$ can be written as a product of as many transpositions as the number of inversions it has, so $sigma$ is even if and only if it has an even number of inversions.
]

== Multilinear Functions
#definition[
  Denote by $V^k = V times dots.c times V$ the Cartesian product of $k$ copies of a real vector space $V$. A function $f: V^k arrow.r RR$ is called *$k$-linear* if it is linear in each of its $k$ arguments:
  $
    f(dots.c, a v + b w, dots.c) = a f(dots.c, v, dots.c) + b f(dots.c, w, dots.c)
  $
  for all $a, b in RR$ and $v, w in V$. Instead of $2$-linear and $3$-linear, it is customary to say *bilinear* and *trilinear*, respectively. \
  A $k$-linear function on $V$ is also called a *$k$-tensor* on $V$. We denote the vector space of all $k$-tensors on $V$ by $L_k (V)$, $k$ is called the *degree* of the tensor $f$. 
]
#example[
  + The dot product $f(v, w) = v dot w$ on $RR^n$ is bilinear. 
  + The determinant $f(v_1, dots.c, v_n) = det[v_1 thick dots.c thick v_n]$ on $RR^n$ is $n$-linear.
]
#definition[
  A $k$-linear function $f: V^k arrow.r RR$ is *symmetric* if
  $
    f(v_sigma(1), dots.c, v_sigma(k)) = f(v_1, dots.c, v_k)
  $
  for all permutations $sigma in S_k$. \
  A $k$-linear function $f: V^k arrow.r RR$ is *alternating* if
  $
    f(v_sigma(1), dots.c, v_sigma(k)) = ["sgn"(sigma)] f(v_1, dots.c, v_k)
  $
  for all permutations $sigma in S_k$.
]
#example[
  + The dot product $f(v, w) = v dot w$ on $RR^n$ is symmetric.
  + The determinant $f(v_1, dots.c, v_n) = det[v_1 thick dots.c thick v_n]$ on $RR^n$ is alternating.
  + The cross product $f(v, w) = v times w$ on $RR^3$ is alternating.
]
We are escpecially interested in the space $A_k (V)$ of all alternating $k$-linear functions on $V$ for $k gt 0$. They are also called *alternating $k$-tensors*, *$k$-covectors*, or *multicovectors of degree $k$* on $V$. 
#definition[
  The vector space of all alternating $k$-linear functions on $V$ is denoted by $A_k (V)$, the elements of $A_k (V)$ are also called *alternating $k$-tensors*, *$k$-covectors*, or *multicovectors of degree $k$* on $V$. \
  For $k = 0$, we define a $0$-covector to be a constant, so $A_0 (V) = RR$. \
  For $k = 1$, a $1$-covector is simply a covector.
]