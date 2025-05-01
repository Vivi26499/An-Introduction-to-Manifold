#import "../Note.typ": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  toc-title: "Chapter 1 Euclidean Spaces",
)
#show ref: theoretic.show-ref
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

== The Permutation Action on Multilinear Functions
#definition[
  If $f in L_k (V)$ and $sigma in S_k$ is a permutation, we define a new $k$-linear function $sigma f$ by
  $
    (sigma f)(v_1, dots.c, v_k) = f(v_sigma(1), dots.c, v_sigma(k)).
  $
  Thus $f$ is symmetric if and only if $sigma f = f$ for all $sigma in S_k$, and $f$ is alternating if and only if $sigma f = ["sgn"(sigma)] f$ for all $sigma in S_k$.
]
When there is only one argument, the permutation group $S_1$ is the identity group and a $1$-linear function is both symmetric and alternating. In particular, 
$
  A_1 (V) = L_1 (V) = V^or.
$
#lemma[
  If $sigma, tau in S_k$ and $f in L_k (V)$, then $tau(sigma f) = (tau sigma) f$.
]
#proof[
  For $v_1, dots.c, v_k in V$, we have
  $
    (tau(sigma f))(v_1, dots.c, v_k) &= (sigma f)(v_tau(1), dots.c, v_tau(k)) \
    &= f(v_sigma(tau(1)), dots.c, v_sigma(tau(k))) \
    &= f(v_((tau sigma)(1)), dots.c, v_((tau sigma)(k))) \
    &= (tau sigma) f(v_1, dots.c, v_k).
  $
]
#definition[
  If $G$ is a group and $X$ is a set, a map
  $
    G times X &arrow.r X, \
    (sigma, x) &arrow.r.bar sigma dot x
  $
  is called a *left action* of $G$ on $X$ if for all $sigma, tau in G$ and $x in X$,
  + $e dot x = x$, where $e$ is the identity element of $G$,
  + $tau dot (sigma dot x) = (tau sigma) dot x$.
  The *orbit* of an element $x in X$ is the set
  $
    G x := {sigma dot x in X | sigma in G}
  $
  A *right action* of $G$ on $X$ is defined similarly: it is a map
  $
    X times G &arrow.r X, \
    (x, sigma) &arrow.r.bar x dot sigma
  $
  such that for all $sigma, tau in G$ and $x in X$,
  + $x dot e = x$, 
  + $(x dot tau) dot sigma = x dot (tau sigma)$.
]
In this terminology, we have defined a left action of $S_k$ on $L_k (V)$.

== The Symmetrizing and Alternating Operators
#definition[
  Given any $k$-linear function $f$ on $V$, we can make a symmetric $k$-linear function $S f$ by
  $
    (S f)(v_1, dots.c, v_k) = sum_(sigma in S_k) f(v_sigma(1), dots.c, v_sigma(k))
  $
  or, in our new sharthand, the *symmetric operator* $S$ is defined by
  $
    S f = sum_(sigma in S_k) sigma f.
  $
  Similarly, the *alternating operator* $A$ is defined by
  $
    A f = sum_(sigma in S_k) ["sgn"(sigma)] sigma f.
  $
]

#proposition(label: <symalt>)[ 
  If $f$ is a $k$-linear function on $V$, then
  + $S f$ is symmetric,
  + $A f$ is alternating.
]
#proof[
  + For $tau in S_k$, we have
  $
    (tau S f) &= sum_(sigma in S_k) tau (sigma f) \
    &= sum_(sigma in S_k) (tau sigma) f \
    &= S f,
  $
  which means $S f$ is symmetric. 
  + For $tau in S_k$, we have
  $
    (tau A f) &= sum_(sigma in S_k) ["sgn"(sigma)] tau (sigma f) \
    &= sum_(sigma in S_k) ["sgn"(sigma)] (tau sigma) f \
    &= ["sgn"(tau)] sum_(sigma in S_k) ["sgn"(tau sigma)] (tau sigma) f \
    &= ["sgn"(tau)] A f,
  $
  which means $A f$ is alternating.
]

#lemma[
  If $f in A_k (V)$, then $A f = (k!) f$.
]
#proof[
  Since $f in A_k (V)$, we have $sigma f = ["sgn"(sigma)] f$ for all $sigma in S_k$. Thus,
  $
    A f &= sum_(sigma in S_k) ["sgn"(sigma)] sigma f \
    &= sum_(sigma in S_k) ["sgn"(sigma)] ["sgn"(sigma)] f \
    &= sum_(sigma in S_k) f \
    &= (k!) f.
  $
]

== The Tensor Product
#definition[
  Let $f in L_k (V)$ and $g in L_l (V)$. The *tensor product* of $f$ and $g$ is the $k + l$-linear function $f times.circle g$ defined by
  $
    (f times.circle g)(v_1, dots.c, v_k, v_(k+1), dots.c, v_(k+l)) = f(v_1, dots.c, v_k) g(v_(k+1), dots.c, v_(k+l)).
  $
]

#example[
  _Bilinear maps_. Let $e_1, dots.c, e_n$ be a basis of $V$, $alpha^1, dots.c, alpha^n$ the dual basis of $V^or$, and
  $
    angle.l thick, thick angle.r: V times V arrow.r RR
  $
  a bilinear map on $V$. Set $g_(i j) = angle.l e_i, e_j angle.r in RR$. If $v = v^i e_i$ and $w = w^i e_i$, with $v^i = alpha^i (v)$, $w^i = alpha^i (w)$ and the bilinearity, we can express $angle.l thick, thick angle.r$ in terms of the tensor product:
  $
    angle.l v, w angle.r &= v^i w^j angle.l e_i, e_j angle.r \
    &= alpha^i (v) alpha^j (w) g_(i j) \
    &= g_(i j) (alpha^i times.circle alpha^j) (v, w).
  $
  Hence, $angle.l thick, thick angle.r = g_(i j) (alpha^i times.circle alpha^j)$. This notation is often used to describe an inner product on $V$.
]

#proposition[
  The tensor product is associative: $(f times.circle g) times.circle h = f times.circle (g times.circle h)$ for multilinear functions $f, g, h$ on $V$.
]
#proof[
  For $f in L_k (V)$, $g in L_l (V)$, and $h in L_m (V)$, we have
  $
    [(f times.circle g) times.circle h](v_1, dots.c, v_(k+l+m)) &= (f times.circle g)(v_1, dots.c, v_(k+l)) h(v_(k+l+1), dots.c, v_(k+l+m)) \
    &= f(v_1, dots.c, v_k) g(v_(k+1), dots.c, v_(k+l)) h(v_(k+l+1), dots.c, v_(k+l+m)) \
    &= f(v_1, dots.c, v_k) (g times.circle h)(v_(k+1), dots.c, v_(k+l+m)) \
    &= [f times.circle (g times.circle h)](v_1, dots.c, v_(k+l+m)),
  $
  which means $(f times.circle g) times.circle h = f times.circle (g times.circle h)$.
]

== The Wedge Product
#definition[
  For $f in A_k (V)$ and $g in A_l (V)$, the *wedge product* or *exterior product* of $f$ and $g$ is the $(k + l)$-linear function $f and g$ defined by
  $
    (f and g) = 1 / (k! l!) A(f times.circle g),
  $
  or explicitly,
  $
    (f and g)(v_1, dots.c, v_(k+l)) = 1 / (k! l!) sum_(sigma in S_(k+l)) ["sgn"(sigma)] f(v_sigma(1), dots.c, v_sigma(k)) g(v_sigma(k+1), dots.c, v_sigma(k+l))
  $<WedgeExplicit>
  By @symalt, the wedge product $f and g in A_(k+l) (V)$
  When $k = 0$, the element $f in A_0(V)$ is a constant $c$, @WedgeExplicit gives
  $
    (c and g)(v_1, dots.c, v_(l)) &= 1 / (0! l!) sum_(sigma in S_(l)) ["sgn"(sigma)] c g(v_sigma(1), dots.c, v_sigma(l)) \
    &= c / (l!) sum_(sigma in S_(l)) ["sgn"(sigma)] g(v_sigma(1), dots.c, v_sigma(l)) \
    &= c g(v_1, dots.c, v_l),
  $
  which means $(c and g) = c g$, is a scalar multiplication.
]
#example[
  For $f in A_2 (V)$ and $g in A_1 (V)$,
  $
    A(f times.circle g) &= f(v_1, v_2) g(v_3) - f(v_1, v_3) g(v_2) - f(v_2, v_1) g(v_3) \
    &+ f(v_2, v_3) g(v_1) + f(v_3, v_1) g(v_2) - f(v_3, v_2) g(v_1),
  $
  where $f(v_1, v_2) g(v_3) = -f(v_2, v_1) g(v_3)$ and so on. \
  Therefore, dividing by $2$, we have
  $
    (f and g)(v_1, v_2, v_3) = f(v_1, v_2) g(v_3) - f(v_1, v_3) g(v_2) + f(v_2, v_3) g(v_1).
  $
]
One way to avoid redundancy in the definition of $f and g$ is to stipulate that in the sum @WedgeExplicit, $sigma(1), dots.c, sigma(k)$ be in ascending order and $sigma(k+1), dots.c, sigma(k+l)$ be in ascending order.
#definition[
  A permutation $sigma in S_(k+l)$ is called a $(k, l)$-*shuffle* if
  $
    sigma(1) lt dots.c lt sigma(k) "and" sigma(k+1) lt dots.c lt sigma(k+l).
  $
]
Then @WedgeExplicit can be rewritten asy
$
  (f and g)(v_1, dots.c, v_(k+l)) = sum_((k, l)-"shuffles" \ sigma) ["sgn"(sigma)] f(v_sigma(1), dots.c, v_sigma(k)) g(v_sigma(k+1), dots.c, v_sigma(k+l)),
$
which is a sum of $mat(k+l; k)$ terms, instead of $(k + l) !$ terms. \
#example[
  For $f, g in A_2 (V)$,
  $
    (f and g)(v_1, v_2, v_3, v_4) &= f(v_1, v_2) g(v_3, v_4) - f(v_1, v_3) g(v_2, v_4) + f(v_1, v_4) g(v_2, v_3) \
    &+ f(v_2, v_3) g(v_1, v_4) - f(v_2, v_4) g(v_1, v_3) + f(v_3, v_4) g(v_1, v_2) \
  $
]

== Anticommutative of the Wedge Product
#proposition[
  The wedge product is *anticommutative*: if $f in A_k (V)$ and $g in A_l (V)$, then
  $
    f and g = (-1)^(k l) g and f.
  $
]
#proof[
  Define $tau in S_(k + l)$ to be the permutation
  $
    tau = mat(1, dots.c, l, l + 1, dots.c, l + k; k + 1, dots.c, k + l, 1, dots.c, k; delim: "[").
  $
  Then
  $
    sigma(1) &= sigma tau (l + 1), dots.c, sigma(k) = sigma tau (l +k), \
    sigma(k + 1) &= sigma tau (1), dots.c, sigma(k + l) = sigma tau (l).
  $
  For any $v_1, dots.c, v_(k + l) in V$, we have
  $
    A(f times.circle g)(v_1, dots.c, v_(k + l)) &= sum_(sigma in S_(k + l)) ["sgn"(sigma)] f(v_sigma(1), dots.c, v_sigma(k)) g(v_sigma(k + 1), dots.c, v_sigma(k + l)) \
    &= sum_(sigma in S_(k + l)) ["sgn"(sigma)] f(v_(sigma tau(l + 1)), dots.c, v_(sigma tau(l + k))) g(v_(sigma tau(1)), dots.c, v_(sigma tau(l))) \
    &= "sgn"(tau) sum_(sigma in S_(k + l)) ["sgn"(sigma tau)] g(v_(sigma tau(1)), dots.c, v_(sigma tau(l))) f(v_(sigma tau(l + 1)), dots.c, v_(sigma tau(l + k))) \
    &= "sgn"(tau) A(g times.circle f)(v_1, dots.c, v_(k + l)),
  $
  which means
  $
    A(f times.circle g) = ["sgn"(tau)] A(g times.circle f).
  $
  Dividing by $k! l!$, we have
  $
    (f and g) = ["sgn"(tau)] (g and f).
  $
  For every $i in [k + 1, k + l], j in [1, k]$, $(i, j)$ is an inversion of $tau$, so $["sgn"(tau)] = (-1)^(k l)$, and therefore
  $
    f and g = (-1)^(k l) g and f.
  $
]
#corollary[
  If $f in A_k (V)$ with odd $k$, then $f and f = 0$.
]
#proof[
  By the anticommutative property of the wedge product, we have
  $
    f and f = (-1)^(k^2) f and f = -f and f,
  $
  which implies that $f and f = 0$.
]

== Associativity of the Wedge Product
#lemma[
  Suppose $f in L_k (V)$ and $g in L_l (V)$, then
  + $A(A(f) times.circle g) = k! A(f times.circle g)$,
  + $A(f times.circle A(g)) = l! A(f times.circle g)$.
]
#proof[
  + By definition,
    $
      A(A(f) times.circle g) &= sum_(sigma in S_(k + l)) ["sgn"(sigma)] sigma ([sum_(tau in S_k) ["sgn"(tau)] tau f] times.circle g) \
      &= sum_(sigma in S_(k + l)) sum_(tau in S_k) ["sgn"(sigma)] ["sgn"(tau)] sigma tau f times.circle g.
    $<lemma>
    For each $mu in S_(k + l)$ and each $tau in S_k$, there is a unique $sigma = mu tau^(-1) in S_(k + l)$ such that $mu = sigma tau$. Then @lemma can be rewritten as
    $
      A(A(f) times.circle g) &= k! sum_(mu in S_(k + l)) ["sgn"(mu)] mu f times.circle g \
      &= k! A(f times.circle g).
    $
  + It can be shown similarly that
    $
      A(f times.circle A(g)) = l! A(f times.circle g).
    $
]

#proposition[
  If $f in A_k (V), g in A_l (V)$ and $h in A_m (V)$, then
  $
    (f and g) and h = f and (g and h)
  $
]
#proof[
  By definition,
  $
    (f and g) and h &= 1 / ((k + l)! m!) A((f and g) times.circle h) \
    &= 1 / ((k + l)! m!) 1 / (k! l!) A(A(f times.circle g) times.circle h) \
    &= (k + l)! / ((k + l)! m! k! l!) A((f times.circle g) times.circle h) \
    &= 1 / (k! l! m!) A((f times.circle g) times.circle h).
  $
  Similarly,
  $
    f and (g and h) &= 1 / (k! (l + m)!) 1 / (l! m!) A(f times.circle (g times.circle h)) \
    &= 1 / (k! l! m!) A(f times.circle (g times.circle h)).
  $
  Since $(f times.circle g) times.circle h = f times.circle (g times.circle h)$, we have
  $
    (f and g) and h = f and (g and h).
  $
]
By associativity, we can omit parentheses and simply write $f and g and h$.
#corollary(label: <associativity>)[
  For $f_i in A_(d_i) (V)$, 
  $
    f_1 and dots.c and f_r = 1 / ((d_1) ! dots.c (d_r) !) A(f_1 times.circle dots.c times.circle f_r).
  $
]

#proposition(label: <determinant>)[
  If $alpha^1, dots.c, alpha^k in V^or$ and $v_1, dots.c, v_k in V$, then
  $
    (alpha^1 and dots.c and alpha^k)(v_1, dots.c, v_k) = det[alpha^i (v_j)],
  $
  where $[alpha^i (v_j)]$ is the matrix whose $(i, j)$th entry is $alpha^i (v_j)$.
]
#proof[
  By @associativity, we have
  $
    (alpha^1 and dots.c and alpha^k)(v_1, dots.c, v_k) &= A(alpha^1 times.circle dots.c times.circle alpha^k)(v_1, dots.c, v_k) \
    &= sum_(sigma in S_k) ["sgn"(sigma)] alpha^1 (v_(sigma(1))) dots.c alpha^k (v_(sigma(k))) \
    &= det[alpha^i (v_j)]
  $
]

#definition[
  An algebra $A$ over a field $K$ is said to be *graded* if it can be written as a direct sum $A = xor_(k=0)^infinity A^k$ over $K$ such that the multiplication map sends $A^k times A^l$ into $A^(k + l)$. The notation $A = xor_(k=0)^infinity A^k$ means that each nonzero element of $A$ can be written uniquely as a finite sum
  $
    a = a_i_1 + dots.c + a_i_m,
  $
  where $a_i_j eq.not 0 in A^(i_j)$. \
  A graded algebra $A = xor_(k=0)^infinity A^k$ is called *anticommutative* or *graded commutative* if for all $a in A^k$ and $b in A^l$,
  $
    a b = (-1)^(k l) b a.
  $
  A *homomorphism* of graded algebras is an algebra homomorphism that preserves the degree.
]

#example[
  The polynomial algebra $A = RR[x, y]$ is graded by degree; $A^k$ consists of all homogeneous polynomials of total degree $k$ in $x$ and $y$.
]

#definition[
  For a finite-dimensional vector space $V$, say of dimension $n$, the *exterior algebra* or *Grassmann algebra* of multivectors on $V$ is the graded algebra
  $
    A_* (V) = xor.big_(k=0)^infinity A_k (V) = xor.big_(k=0)^n A_k (V),
  $
  with the wedge product as multiplication.
]

== A Basis for $k$-Covectors
Let $e_1, dots.c, e_n$ be a basis for $V$ and $alpha^1, dots.c, alpha^n$ be the dual basis for $V^or$. Introduce the multi-index notation
$
  I = (i_1, dots.c, i_k) 
$
and write $e_I$ for $(e_(i_1), dots.c, e_(i_k))$ and $alpha^I$ for $(alpha^(i_1), dots.c, alpha^(i_k))$. \
A $k$-linear function $f$ on $V$ is completely determined by its values on all $k$-tuples $(e_i_1, dots.c, e_i_k)$. If $f$ is alternating, then it is completely determined by its values on $(e_i_1, dots.c, e_i_k)$ with $1 lt.eq i_1 lt dots.c lt i_k lt.eq n$; that is, it suffices to consider $e_I$ with $I$ in strictly ascending order.

#lemma[
  Let $e_1, dots.c, e_n$ be a basis for $V$ and $alpha^1, dots.c, alpha^n$ be the dual basis for $V^or$. If $I = (1 lt.eq i_1 lt dots.c lt i_k lt.eq n)$ and $J = (1 lt.eq j_1 lt dots.c lt j_k lt.eq n)$ are two strictly ascending multi-indices of length $k$, then
  $
    alpha^I (e_J) = delta^I_J = cases(
      1 &"for" I = J,
      0 &"for" I eq.not J.
    )
  $
]
#proof[
  By @determinant,
  $
    alpha^I (e_J) = det[alpha^i (e_j)]_(i in I, j in J).
  $
  If $I = J$, $[alpha^i (e_j)]$ is the identity matrix, so $alpha^I (e_J) = 1$. \
  If $I eq.not J$, we compare them term by term until th terms differ:
  $
    i_1 = j_1, dots.c, i_(l-1) = j_(l-1), i_l eq.not j_l, dots.c .
  $
  Without loss of generality, we can assume $i_l < j_l$. Then $i_l eq.not j_1, dots.c, j_(l-1)$, and $i_l eq.not j_(l+1), dots.c, j_k$, so the $l$-th row of $[alpha^i (e_j)]$ will be all zeros. Thus, $alpha^I (e_J)=0.$
]

#proposition[
  The alternating $k$-linear function $alpha^I, I = (i_1 lt dots.c lt i_k)$, form a basis for $A_k (V)$.
]
#proof[
  To show linear independence, suppose $c_I alpha^I = 0$ for some $c_I in RR$. Applying both sides to $e_J$ gives
  $
    0 &= c_I alpha^I (e_J) \
    &= c_I delta^I_J \
    &= c_J,
  $
  which means $c_J = 0$ for all $J$, so $alpha^I$ are linearly independent. \
  To show that they span $A_k (V)$, let $f in A_k (V)$ and $g = f(e_I) alpha^I$. Then
  $
    g(e_J) &= f(e_I) alpha^I (e_J) \
    &= f(e_I) delta^I_J \
    &= f(e_J),
  $
  which means $f = g = f(e_I) alpha^I$, so $f$ is a linear combination of $alpha^I$. Thus, $alpha^I$ span $A_k (V)$.
]

#corollary[
  If $V$ is $n$-dimensional, then the dimension of $A_k (V)$ is $mat(n; k)$.
]

#corollary[
  If $k gt dim V$, then $A_k (V) = 0$.
]

= Differential Forms on $RR^n$