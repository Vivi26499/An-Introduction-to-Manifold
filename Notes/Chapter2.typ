#import "../Note.typ": *

#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  toc-title: "Chapter 2 Manifolds",
  chapter: 2
)
#counter(heading).update(4)

We are concerned mainly with smooth manifolds.

= Smooth Functions on a Euclidean Space

== Topological Manifolds
#definition[
  A topological space is *second countable* if it has a countable base.
]
#definition[
  A *neighborhood* of a point $p$ in a topological space $M$ is any open set $U subset M$ such that $p in U$.
]
#definition[
  An *open cover* of a topological space $M$ is a collection ${U_alpha}_(alpha in A)$ of open sets such that $M = union.big_(alpha in A) U_alpha$.
]
#definition[
  A topological space $M$ is *locally Euclidean of dimension $n$* if every point $p in M$ has a neighborhood $U$ such that there is a homeomorphism $phi.alt$ from $U$ to an open subset of $R^n$. \
  The pair $(U, phi.alt:U arrow RR^n)$ is called a *chart* of $M$ at $p$, $U$ is called the *coordinate neighborhood* or *coordinate open set* of $p$, and $phi.alt$ is called the *coordinate map* or *coordinate system* on $U$. A chart $(U, phi.alt)$ is *centered* at $p in U$ if $phi.alt(p) = 0$.
]
#definition[
  A *topological manifold* is a Hausdorff, second countable, locally Euclidean space. It is of *dimension $n$* if it is locally Euclidean of dimension $n$.
]

#corollary(title: "invarience of dimension")[
  An open subset of $RR^n$ is not homeomorphic to an open subset of $RR^m$ if $n != m$.
]

If a topological space has several connected components, it is possible for each component to have a different dimension. 
#example[
  The Euclidean space $RR^n$ is covered by a single chart $(RR^n, bb(1)_(RR^n))$, where $bb(1)_(RR^n): RR^n arrow RR^n$ is the identity map. Every open subset of $RR^n$ is also a topological manifold, with chart $(U, bb(1)_(U))$.
]

#proposition[
  The Hausdorff condition and second countability are "hereditary" properties, i.e.,
  + A subspace of a Hausdorff space is Hausdorff,
  + A subspace of a second-countable space is second countable.
]

#example(title: "A cusp")[
  The graph of $y = x^(2/3)$ in $RR^2$ is a topological manifold. By virtue of being a subspace of $RR^2$, it is Hausdorff and second countable. It is locally Euclidean of dimension 1, since it is homeomorphic to $RR$ via $(x, x^(2/3)) mapsto x$ 
]

#example(title: "A cross")[
  The cross in $RR^2$ with subspace topology is not locally Euclidean at the intersection $p$, and so cannot be a topological manifold.
]
#sol[
  Suppoese the cross is locally Euclidean of dimension $n$ at $p$. Then there is a neighborhood $U$ of $p$ homeomorphic to an open ball $B:= B(0, epsilon) subset RR^n$ with $p$ mapping to $0$. Then $U - {p}$ is homeomorphic to $B - {0}$. Since $B - {0}$ is connected if $n gt.eq 2$ or has two connected components if $n = 1$, but $U - {p}$ has $4$ connected components, $U - {p}$ cannot be homeomorphic to $B - {0}$, contradicting the assumption that $U$ is homeomorphic to $B$.
]

== Compatible Charts
Suppose $(U, phi.alt: U arrow RR^n)$ and $(V, psi: V arrow RR^n)$ are two charts of a topological manifold. Since $U inter V$ is open in $U$, the image $phi.alt(U inter V)$ is open in $RR^n$. Similarly, $psi(U inter V)$ is open in $RR^n$. 

#definition[
  Two charts $(U, phi.alt: U arrow RR^n), (V, psi: V arrow RR^n)$ of a topological manifold are *$C^infinity$-compatible* if the two maps
  $
    phi.alt compose psi^(-1): psi(U inter V) arrow phi.alt(U inter V), quad psi compose phi.alt^(-1): phi.alt(U inter V) arrow psi(U inter V)
  $
  are $C^infinity$. These two maps are called the *transition functions* between the charts $(U, phi.alt)$ and $(V, psi)$. If $U inter V$ is empty, then the two charts are automatically $C^infinity$-compatible. To simplify the notation, we will write $U_(alpha beta)$ for $U_alpha inter U_beta$ and $U_(alpha beta gamma)$ for $U_alpha inter U_beta inter U_gamma$. \
  Since we are interested only in $C^infinity$-compatible charts, we often omit mention of "$C^infinity$" and speak simply of "compatible charts".
]

#definition[
  A *$C^infinity$ atlas* or simply an *atlas* on a locally Euclidean space $M$ is a collection $frak(U) = {(U_alpha, phi.alt_alpha)}$ of pairwise $C^infinity$-compatible charts that cover $M$, i.e., $M = union.big_alpha U_alpha$.
]

#example[
  The Unit circle $S^1$ in the complex plane $CC$ may by described as the set of points ${e^(i t) in CC | 0 lt.eq t lt.eq 2 pi}$. Let $U_1$ and $U_2$ be the open sets of $S^1$ defined by
  $
    U_1 &= {e^(i t) in CC | - pi lt t lt pi}, \
    U_2 &= {e^(i t) in CC | 0 lt t lt 2 pi},
  $
  and $phi.alt_alpha: U_alpha arrow RR$ for $alpha = 1, 2$ by
  $
    phi.alt_1(e^(i t)) &= t, quad -pi lt t lt pi, \
    phi.alt_2(e^(i t)) &= t, quad 0 lt t lt 2 pi,
  $
  where $phi.alt_1$ and $phi.alt_2$ are both homeomorphisms from $U_1$ and $U_2$ to open subsets of $RR$. Thus, $(U_1, phi.alt_1)$ and $(U_2, phi.alt_2)$ are charts on $S^1$. The intersection $U_1 inter U_2$ consists of two connected components, 
  $
    A &= {e^(i t) | - pi lt t lt 0}, \
    B &= {e^(i t) | 0 lt t lt pi},
  $
  with 
  $
    phi.alt_1(U_1 inter U_2) = phi.alt_1(A union.sq B) = phi.alt_1(A) union.sq phi.alt_1(B) = (-pi, 0) union.sq (0, pi), \
    phi.alt_2(U_1 inter U_2) = phi.alt_2(A union.sq B) = phi.alt_2(A) union.sq phi.alt_2(B) = (pi, 2pi) union.sq (0, pi),
  $
  where $union.sq$ denotes the disjoint union. The transition functions are given by
  $
    (phi.alt_2 compose phi.alt_1^(-1))(t) &= cases(
      t + 2 pi quad &"for" t in (-pi, 0), 
      t &"for" t in (0, pi), 
    ), \
    (phi.alt_1 compose phi.alt_2^(-1))(t) &= cases(
      t - 2 pi quad &"for" t in (pi, 2 pi), 
      t &"for" t in (0, pi), 
    ),
  $
  which means that the charts $(U_1, phi.alt_1)$ and $(U_2, phi.alt_2)$ are $C^infinity$-compatible and then form a $C^infinity$ atlas.
]

#remark[
  Although the $C^infinity$ compatibility of charts is clearly reflexive and symmetric, it is not transitive. For example, Suppose $(U_1, phi.alt_1)$ is $C^infinity$-compatible with $(U_2, phi.alt_2)$ and $(U_2, phi.alt_2)$ is $C^infinity$-compatible with $(U_3, phi.alt_3)$. Then the composite
  $
    phi.alt_3 compose phi.alt_1^(-1) = (phi.alt_3 compose phi.alt_2^(-1)) compose (phi.alt_2 compose phi.alt_1^(-1))
  $
  is $C^infinity$, but only on $phi.alt_1(U_(123))$, not necessarily on $phi.alt_1(U_(13))$. 
]

#definition[
  A chart $(V, psi)$ is *compatible* with an atlas ${(U_alpha, phi.alt_alpha)}$ if it is compatible with all the charts $(U_alpha, phi.alt_alpha)$ of the atlas.
]
#lemma(label: <compatible>)[
  Let ${(U_alpha, phi.alt_alpha)}$ be an atlas on a locally Euclidean space $M$. If two charts $(V, psi)$ and $(W, sigma)$ are both compatible with the atlas ${(U_alpha, phi.alt_alpha)}$, then they are compatible with each other.
]
#proof[
  Let $p in V inter W$. Since ${(U_alpha, phi.alt_alpha)}$ is an atlas for $M$, $p in U_alpha$ for some $alpha$, then $p in V inter W inter U_alpha$. The composite
  $
    sigma compose psi^(-1) &= (sigma compose phi.alt_alpha^(-1)) compose (phi.alt_alpha compose psi^(-1))
  $
  is $C^infinity$ on $psi(V inter W inter U_alpha)$, hence at $psi(p)$. Since $p$ is arbitrary, the composite $sigma compose psi^(-1)$ is $C^infinity$ on $psi(V inter W)$. Similarly, $psi compose sigma^(-1)$ is $C^infinity$ on $psi(V inter W)$. Thus, the charts $(V, psi)$ and $(W, sigma)$ are compatible.
]

== Smooth Manifolds
#definition[
  An atlas $frak(M)$ on a locally Euclidean space $M$ is *maximal* if it is not contained in a larger atlas, i.e., if $frak(M) subset.eq frak(U)$, then $frak(M) = frak(U)$.
]

#definition[
  A *smooth manifold* or *$C^infinity$ manifold* is a topological manifold $M$ together with a maximal atlas $frak(M)$. The maximal atlas $frak(M)$ is called the *differential structure* on $M$. A manifold is said to have dimension $n$ if all of its connected components have dimension $n$. A $1$-dimensional manifold is called a *curve*, a $2$-dimensional manifold is called a *surface*, and an $n$-dimensional manifold is called an *$n$-manifold*.
]

In parctice, to check that a topological manifold $M$ is a smooth manifold, it is not necessary to exhibit a maximal atlas. The existence of _any_ atlas on $M$ will do.

#proposition[
  Any atlas $frak(U) = {(U_alpha, phi.alt_alpha)}$ on a locally Euclidean space $M$ is contained in a unique maximal atlas.
]
#proof[
  Adjoin to the atlas $frak(U)$ all charts $(V_i, psi_i)$ that are compatible with $frak(U)$. By @compatible the charts $(V_i, psi_i)$ are compatible with each other. So the enlarged collection $frak(U) union {(V_i, psi_i)}$ is an atlas on $M$. Any chart compatible with the new atlas is compatible with $frak(U)$, and so is contained in the new atlas. Thus, the new atlas is maximal. \
  Let $frak(M)_1, frak(M)_2$ be two maximal atlases containing $frak(U)$. Then all the charts of $frak(M)_1$ are compatible with $frak(U)$, then must belong to $frak(M)_2$, i.e., $frak(M)_1 subset.eq frak(M)_2$. Similarly, $frak(M)_2 subset.eq frak(M)_1$. Thus, $frak(M)_1 = frak(M)_2$, i.e., the maximal atlas containing $frak(U)$ is unique.
]

In summary, to show that a topological manifold $M$ is a $C^infinity$ manifold, it is sufficient to check that
+ $M$ is Hausdorff and second countable,
+ $M$ has a $C^infinity$ atlas (not necessarily maximal).
From now on, a "manifold" will mean a $C^infinity$ manifold, with the terms "smooth" and "$C^infinity$" used interchangeably.
#definition[
  In the context of manifolds, we denote the standard coordinates on $RR^n$ by $r^1, dots.c, r^n$. If $(U, phi.alt: U arrow RR^n)$ is a chart of a manifold, we let $x^i = r^i compose phi.alt$ be the $i$th component of $phi.alt$ and write $phi.alt = (x^1, dots.c, x^n)$ and $(U, phi.alt) = (U, x^1, dots.c, x^n)$. For $p in U$, $x^1(p), dots.c, x^n (p)$ is a point in $RR^n$. The functions $x^1, dots.c, x^n$ are called *coordinates* or *local coordinates* on $U$. By abuse of notation, we sometimes omit the $p$. So the notation $(x^1, dots.c, x^n)$ stands alternately for local coordinates on $U$ or for a point in $RR^n$. A chart $(U, phi.alt)$ *about* $p in M$ is a chart in the differential structure of $M$ such that $p in U$. 
]

== Examples of Smooth Manifolds
#example(title: "Euclidean space")[
  The Euclidean space $RR^n$ is a smooth manifold with a single chart $(RR^n, r^1, dots.c, r^n)$, where $r^1, dots.c, r^n$ are the standard coordinates on $RR^n$.
]

#example(title: "Open subsets of a manifold")[
  Any open subset $V subset M$ of a manifold $M$ is also a manifold. If ${(U_alpha, phi.alt_alpha)}$ is an atlas on $M$, then ${(U_alpha inter V, phi.alt_alpha|_(U_alpha inter V))}$ is an atlas on $V$, where $phi.alt_alpha|_(U_alpha inter V): U_alpha inter V arrow RR^n$ denotes the restriction of $phi.alt_alpha$ to $U_alpha inter V$.
]

#example(title: "Manifolds of dimension zero")[
  In a manifold of dimension zero, every singleton subset is homeomorphic to $RR^0$ and so is open. Thus, a zero-dimensional manifold is a discrete set. By second countability, this discrete set is countable. \
]

#example(title: "Graph of a smooth function")[
  For a subset $A in RR^n$ and a function $f: A arrow RR^m$, the *graph* of $f$ is defined to be the subset
  $
    Gamma(f) = {(x, f(x)) in A times RR^m }.
  $
  If $U$ is an open subset of $RR^n$ and $f: U arrow RR^m$ is $C^infinity$, then the two maps
  $
    phi.alt: Gamma(f) &arrow U \
    (x, f(x)) &mapsto x,
  $
  and
  $
    (1, f): U &arrow Gamma(f) \
    x &mapsto (x, f(x)),
  $
  are continuous and inverse to each other, and so are homeomorphisms. The graph $Gamma(f)$ of $f: U arrow RR^m$ has an atlas with a single chart $(Gamma(f), phi.alt)$, and is therefore a $C^infinity$ manifold.
]

#example(title: "General linear group")[
  For any two positive integers $m, n$, let $RR^(m times n)$ be the vector space of all $m times n$ matrices. The *general linear group* $"GL"(n, RR)$ is defined by
  $
    "GL"(n, RR) = {A in RR^(n times n) | det A eq.not 0} = scripts(det)^(-1)( RR - {0}).
  $
  Since the determinant function is continuous, $"GL"(n, RR)$ is an open subset of $RR^(n times n) tilde.eq RR^(n^2)$ and is therefore a manifold of dimension $n^2$. \
  The *complex general linear group* $"GL"(n, CC)$ is defined to be the group of nonsingular $n times n$ complex matrices. Since an $n times n$ matrix $A$ is nonsingular if and only if $det A eq.not 0$, $"GL"(n, CC)$ is an open subset of $CC^(n times n) tilde.eq RR^(2n^2)$ and is therefore a manifold of dimension $2n^2$.
]  

#example(title: "Unit circle in the (x, y)-plane", label: <UnitCircle>)[
  We now view $S^1$ as the unit circle in the real plane $RR^2$ with defining equation
  $
    x^2 + y^2 = 1.
  $
  We can cover $S^1$ with four open sets
  $
    U_1 &= {(x, sqrt(1 - x^2)) | -1 lt x lt 1}, \
    U_2 &= {(x, -sqrt(1 - x^2)) | -1 lt x lt 1}, \
    U_3 &= {(sqrt(1 - y^2), y) | -1 lt y lt 1}, \
    U_4 &= {(-sqrt(1 - y^2), y) | -1 lt y lt 1},
  $
  with maps
  $
    phi.alt_1(x, y) &= phi.alt_2(x, y) = x, \
    phi.alt_3(x, y) &= phi.alt_4(x, y) = y.
  $
  The transition functions are given by
  $
    (phi.alt_3 compose phi.alt_1^(-1))(x) &= phi.alt_3(x, sqrt(1 - x^2)) = sqrt(1 - x^2), \
    (phi.alt_4 compose phi.alt_1^(-1))(x) &= phi.alt_4(x, sqrt(1 - x^2)) = sqrt(1 - x^2), \
    (phi.alt_3 compose phi.alt_2^(-1))(x) &= phi.alt_3(x, -sqrt(1 - x^2)) = -sqrt(1 - x^2), \
    (phi.alt_4 compose phi.alt_2^(-1))(x) &= phi.alt_4(x, -sqrt(1 - x^2)) = -sqrt(1 - x^2),
  $
  etc. which are all $C^infinity$. Thus ${(U_i, phi.alt_i)}_(i=1)^4$ is a $C^infinity$ atlas on $S^1$.
]

#proposition(title: "An atlas for a product manifold")[
  If ${(U_alpha, phi.alt_alpha)}$ and ${(V_i, psi_i)}$ are $C^infinity$ atlases for the manifolds $M$ and $N$ of dimensions $m$ and $n$, respectively, then the collection
  $
    {(U_alpha times V_i, phi.alt_alpha times psi_i: U_alpha times V_i arrow RR^m times RR^n)}
  $
  of charts is a $C^infinity$ atlas on $M times N$. Therefore $M times N$ is a $C^infinity$ manifold of dimension $m + n$.
]
#proof[
  Since ${(U_alpha, phi.alt_alpha)}$ and ${(V_i, psi_i)}$ are $C^infinity$ atlases for the manifolds $M$ and $N$, respectively, the charts $(U_alpha, phi.alt_alpha)$ and $(V_i, psi_i)$ are $C^infinity$-compatible and cover $M$ and $N$, respectively, i.e., $M = union.big_alpha U_alpha$ and $N = union.big_i V_i$. \
  For any $p times q in M times N$, there are $p in U_alpha$ and $q in V_i$, then $p times q in U_alpha times V_i$, i.e., $M times N = union.big_(alpha, i) (U_alpha times V_i)$. \
  For $(U_alpha, phi.alt_alpha: U_alpha arrow tilde(U)_alpha subset RR^m)$ and $(V_i, psi_i: V_i arrow tilde(V)_i subset RR^n)$, the product map $phi.alt_alpha times psi_i: U_alpha times V_i arrow tilde(U)_alpha times tilde(V)_i subset RR^m times RR^n tilde.eq RR^(m +n)$ is a homeomorphism as the product of homeomorphisms. \
  For $U_alpha times V_i, U_beta times V_j subset M times N$, and suppose $(U_alpha times V_i) inter (U_beta times V_j) eq.not diameter$. The transition functions
  $
    (phi.alt_beta times psi_j) compose (phi.alt_alpha times psi_i)^(-1) &= (phi.alt_beta compose phi.alt_alpha^(-1)) times (psi_j compose psi_i^(-1)), \
    (phi.alt_alpha times psi_i) compose (phi.alt_beta times psi_j)^(-1) &= (phi.alt_alpha compose phi.alt_beta^(-1)) times (psi_i compose psi_j^(-1)),
  $
  are $C^infinity$ because the compositions are $C^infinity$ and the products of $C^infinity$ functions are $C^infinity$. \
  Thus, the collection ${(U_alpha times V_i, phi.alt_alpha times psi_i)}$ is a $C^infinity$ atlas on $M times N$. The dimension of $M times N$ is $m + n$.
]

#example[
  The infinite cylinder $S^1 times RR$ and the torus $S^1 times S^1$ are smooth manifolds of dimensions $2$.
]

Since $M times N times P = (M times N) times P$ is the successive product of spaces, if $M, N, P$ are manifolds, then so is $M times N times P$. Thus, the $n$- dimensional torus $S^1 times dots.c times S^1$ is a manifold of dimension $n$.

#remark[
  Let $S^n$ be the unit sphere
  $
    (x^1)^2 + (x^2)^2 + dots.c + (x^(n+1))^2 = 1
  $
  in $RR^(n+1)$. Using @UnitCircle[-], it is easy to write down a $C^infinity$ atlas for $S^n$, showing that $S^n$ has a differential structure. The manifold $S^n$ with this differential structure is called the *standard $n$-sphere*.
]

= Smooth Maps on a Manifold
By the $C^infinity$ compatibility of charts in an atlas, the smoothness of a map between two manifolds is independent of the choice of charts and is therefore well defined.

== Smooth Functions on a Manifold
#definition(label: <SmoothMaponManifold>)[
  Let $M$ be a smooth manifold of dimension $n$. A function $f: M arrow RR$ is said to be *smooth* or *$C^infinity$* at a point $p in M$ if there is a chart $(U, phi.alt)$ about $p$ such that the composite
  $
    f compose phi.alt^(-1): phi.alt(U) arrow RR
  $
  is $C^infinity$ at $phi.alt(p)$. The function $f$ is said to be $C^infinity$ on $M$ if it is $C^infinity$ at every point of $M$.
]

#remark(label: <SmoothnessIndependence>)[
  The definition of smoothness of a function $f$ at a point is independent of the chart $(U, phi.alt)$, for if $f compose phi.alt^(-1)$ is $C^infinity$ at $phi.alt(p)$, and $(V, psi)$ any other chart about $p$, then on $psi(U inter V)$, the composite
  $
    f compose psi^(-1) = (f compose phi.alt^(-1)) compose (phi.alt compose psi^(-1)) 
  $
  is $C^infinity$ at $psi(p)$.
]

In @SmoothMaponManifold, $f: M arrow RR$ is not assumed to be continuous. However, if $f$ is $C^infinity$ at $p in M$, then $f compose phi.alt^(-1): phi.alt(U) arrow RR$, being a $C^infinity$ function at $phi.alt(p)$ in an open subset of $RR^n$, is continuous at $phi.alt(p)$. As a composite of continuous functions, $f = (f compose phi.alt^(-1)) compose phi.alt$ is continuous at $p$. Since we are interested only in functions that are $C^infinity$ on an open set, there is no loss of generality in assuming at the outset that $f$ is continuous. 

#proposition(title: [Smoothness of a real-valued function])[
  Let $M$ be a smooth manifold of dimension $n$ and $f: M arrow RR$ a real-valued function on $M$. The following are equivalent:
  + The function $f: M arrow RR$ is $C^infinity$.
  + The manifold $M$ has an atlas such that for every chart $(U, phi.alt)$ in the atlas, the composite
    $
      f compose phi.alt^(-1): RR^n supset phi.alt(U) arrow RR
    $
    is $C^infinity$.
  + For every chart $(V, psi)$ on $M$, the composite
    $
      f compose psi^(-1): RR^n supset psi(U) arrow RR
    $
    is $C^infinity$.
]
#proof[
  We can prove the proposition as a cycle chain of implications. \
  (ii) $arrow.double$ (i): This follows directly from the definition of a $C^infinity$ function, since by (ii) every point $p in M$ has a chart $(U, phi.alt)$ about it such that $f compose phi.alt^(-1)$ is $C^infinity$ at $phi.alt(p)$. \
  (i) $arrow.double$ (iii): Let $p in M$ and $(V, psi)$ be a chart about $p$. By @SmoothnessIndependence,  $f compose psi^(-1)$ is $C^infinity$ at $psi(p)$. Since $p$ is arbitrary, $f compose psi^(-1)$ is $C^infinity$ on $psi(V)$. \
  (iii) $arrow.double$ (ii): Obvious.
]

#definition[
  Let $F: N arrow M$ be a map and $h$ a function on $M$. The *pullback* of $h$ by $F$,denoted by $F^*h$, is the composite function
  $
    F^*h = h compose F: N arrow RR.
  $
]

In this terminology, a function $f$ on $M$ is $C^infinity$ on a chart $(U, phi.alt)$ if and only if its pullback $(phi.alt^(-1))^*f$ is $C^infinity$ on the subset $phi.alt(U) subset RR^n$.

== Smooth Maps Between Manifolds
#definition(label: <SmoothMapBetweenManifolds>)[
  Let $N$ and $M$ be manifolds of dimensions $n$ and $m$, respectively. A continuous map $F: N arrow M$ is $C^infinity$ at a point $p in N$ if there are charts $(V, psi)$ about $F(p) in M$ and $(U, phi.alt)$ about $p in N$ such that the composite
  $
    psi compose F compose phi.alt^(-1): RR^n supset phi.alt(F^(-1)(V) inter U) arrow RR^m
  $
  is $C^infinity$ at $phi.alt(p)$. The continuous map $F: N arrow M$ is said to be $C^infinity$ on $N$ if it is $C^infinity$ at every point of $N$.
]
In @SmoothMapBetweenManifolds, we assume $F: N arrow M$ is continuous to ensure that $F^(-1)(V)$ is open in $N$. Thus, $C^infinity$ maps are by definition continuous.

#remark(title: [Smooth maps into $RR^m$])[
  In case $M = RR^m$, we can take $(RR^m, bb(1_(RR^m)))$ as a chart about $F(p)$ in $M$. According to @SmoothMapBetweenManifolds, $F: N arrow RR^m$ is $C^infinity$ at $p in N$ if and only if there is a chart $(U, phi.alt)$ about $p in N$ such that the composite
  $
    F compose phi.alt^(-1): RR^n supset phi.alt(U) arrow RR^m
  $
  is $C^infinity$ at $phi.alt(p)$. Letting $m = 1$, we recover the definition of a function being $C^infinity$ at a point in @SmoothMaponManifold.
]

#proposition(label: <SmoothMapBetweenManifolds:Charts>)[
  Suppose $F: N arrow M$ is $C^infinity$ at $p in N$. If $(U, phi.alt)$ is any chart about $p in N$ and $(V, psi)$ is any chart about $F(p) in M$, then $psi compose F compose phi.alt^(-1)$ is $C^infinity$ at $phi.alt(p)$.
]
#proof[
  Since $F$ is $C^infinity$ at $p$, there are charts $(U_alpha, phi.alt_alpha)$ about $p in N$ and $(V_i, psi_i)$ about $F(p) in M$ such that $V_i compose F compose phi.alt_alpha^(-1)$ is $C^infinity$ at $phi.alt_alpha (p)$. By the $C^infinity$ compatibility of charts in a differential structure, both $phi.alt_alpha compose phi.alt^(-1)$ and $psi compose psi_i^(-1)$ are $C^infinity$. Hence, the composite
  $
    psi compose F compose phi.alt^(-1) = (psi compose psi_i^(-1)) compose (V_i compose F compose phi.alt_alpha^(-1)) compose (phi.alt_alpha compose phi.alt^(-1))
  $
  is $C^infinity$ at $phi.alt(p)$.
]

#proposition(title: [Smoothness of a map in terms of charts], label: <SmoothnessofMap:Charts>)[
  Let $N$ and $M$ be manifolds of dimensions $n$ and $m$, respectively and $F: N arrow M$ a continuous map. The following are equivalent:
  + The map $F: N arrow M$ is $C^infinity$.
  + There are atlases $frak(U)$ for $N$ and $frak(V)$ for $M$ such that for every chart $(U, phi.alt) in frak(U)$ and $(V, psi) in frak(V)$, the composite
    $
      psi compose F compose phi.alt^(-1): RR^n supset phi.alt(U inter F^(-1)(V)) arrow RR^m
    $
    is $C^infinity$.
  + For every chart $(U, phi.alt)$ on $N$ and $(V, psi)$ on $M$, the composite
    $
      psi compose F compose phi.alt^(-1): RR^n supset phi.alt(U inter F^(-1)(V)) arrow RR^m
    $
    is $C^infinity$.
]
#proof[
  We can prove the proposition as a cycle chain of implications. \
  (ii) $arrow.double$ (i): Let $p in N$ and $(U, phi.alt) in frak(U)$ be a chart about $p$ and $(V, psi) in frak(V)$ a chart about $F(p)$, then $psi compose F compose phi.alt^(-1)$ is $C^infinity$ at $phi.alt(p)$. By @SmoothMapBetweenManifolds, $F: N arrow M$ is $C^infinity$ at $p$. Since $p$ is arbitrary, $F: N arrow M$ is $C^infinity$ on $N$. \
  (i) $arrow.double$ (iii): Let $(U, phi.alt)$ be a chart on $N$ and $(V, psi)$ a chart on $M$ such that $U inter F^(-1)(V) eq.not nothing$. Let $p in U inter F^(-1)(V)$, then $(U, phi.alt)$ is a chart about $p$ and $(V, psi)$ is a chart about $F(p)$. By @SmoothMapBetweenManifolds:Charts, $psi compose F compose phi.alt^(-1)$ is $C^infinity$ at $phi.alt(p)$. Since $p$ is arbitrary, $phi.alt(p)$ is arbitrary, $psi compose F compose phi.alt^(-1)$ is $C^infinity$ on $phi.alt(U inter F^(-1)(V))$. \
  (iii) $arrow.double$ (ii): Obvious.
]

#proposition(title: [Composition of $C^infinity$ maps])[
  If $F: N arrow M$ and $G: M arrow P$ are $C^infinity$ maps between manifolds, then the composite $G compose F: N arrow P$ is $C^infinity$.
]
#proof[
  Let $(U, phi.alt), (V, psi), (W, sigma)$ be charts on $N, M, P$, respectively. Then
  $
    sigma compose (G compose F) compose phi.alt^(-1) = (sigma compose G compose psi^(-1)) compose (psi compose F compose phi.alt^(-1)).
  $
  Since $F$ and $G$ are $C^infinity$, by @SmoothnessofMap:Charts[-](i) $arrow.double$ (iii), $sigma compose G compose psi^(-1)$ and $psi compose F compose phi.alt^(-1)$ are $C^infinity$. As a composite of $C^infinity$ maps of open subsets of Euclidean spaces, $sigma compose (G compose F) compose phi.alt^(-1)$ is $C^infinity$. By @SmoothnessofMap:Charts[-](iii) $arrow.double$ (i), $G compose F: N arrow P$ is $C^infinity$.
]

== Diffeomorphisms
#definition[
  A *diffeomorphism* of manifolds is a bijective $C^infinity$ map $F: N arrow M$ whose inverse $F^(-1)$ is also $C^infinity$. 
]
According to the next two propositions, coordinate maps are diffeomorphisms, and conversely, every diffeomorphism of an open subset of a manifold with an open subset of Euclidean space can serve as a coordinate map.

#proposition(label: <CoordMapDiffeo>)[
  If $(U, phi.alt)$ is a chart on a manifold $M$ of dimension $n$, then the coordinate map $phi.alt: U arrow phi.alt(U) subset RR^n$ is a diffeomorphism.
]
#proof[
  By definition, $phi.alt$ is a homeomorphism, so it suffices to check that both $phi.alt$ and $phi.alt^(-1)$ are $C^infinity$. \
  We use the atlas ${(U, phi.alt)}$ with a single chart on $U$ and atlas ${(phi.alt(U), bb(1)_(phi.alt(U)))}$ with a single chart on $phi.alt(U)$. Since
  $
    bb(1)_(phi.alt(U)) = bb(1)_(phi.alt(U)) compose phi.alt compose phi.alt^(-1): phi.alt(U) arrow phi.alt(U) 
  $
  is the identity map, it is $C^infinity$. By @SmoothnessofMap:Charts[-](ii) $arrow.double$ (i), $phi.alt$ is $C^infinity$. \
  Similarly, $phi.alt^(-1)$ is $C^infinity$ because
  $
    bb(1)_(U) = phi.alt compose phi.alt^(-1) compose bb(1)_(phi.alt(U)): U arrow U
  $
  is $C^infinity$.
]

#proposition(label: <DiffeoCoordMap>)[
  Let $U$ be an open subset of a manifold $M$ of dimension $n$. If $F: U arrow F(U) subset RR^n$ is a diffeomorphism onto an open subset of $RR^n$, then $(U, F)$ is a chart in the differential structure of $M$.
]
#proof[
  For any chart $(U_alpha, phi.alt_alpha)$ in the maximal atlas of $M$, both $phi.alt_alpha$ and $phi.alt_alpha^(-1)$ are $C^infinity$ by @CoordMapDiffeo[-]. As composites of $C^infinity$ maps, $F compose phi.alt_alpha^(-1)$ and $phi.alt_alpha compose F^(-1)$ are $C^infinity$. Hence, $(U, F)$ is compatible with the maximal atlas, i.e., $(U, F)$ is a chart in the differential structure of $M$.
]

== Smoothness in Terms of Components
#proposition(title: [Smoothness of a vector-valued function], label: <SmoothnessVecValued>)[
  Let $N$ be a manifold and $F: N arrow RR^m$ a continuous map. The following are equivalent:
  + The map $F: N arrow RR^m$ is $C^infinity$.
  + The manifold $N$ has an atlas such that for every chart $(U, phi.alt)$ in the atlas, the composite
    $
      F compose phi.alt^(-1): phi.alt(U) arrow RR^m
    $
    is $C^infinity$.
  + For every chart $(U, phi.alt)$ on $N$, the composite
    $
      F compose phi.alt^(-1): phi.alt(U) arrow RR^m
    $
    is $C^infinity$.
]
#proof[
  We can prove the proposition as a cycle chain of implications. \
  (ii) $arrow.double$ (i): Let ${(RR^m, bb(1)_(RR^m))}$ be the atlas on $RR^m$ with a single chart, then
  $
    F compose phi.alt^(-1) = bb(1)_(RR^m) compose F compose phi.alt^(-1): phi.alt(U) arrow RR^m
  $
  is $C^infinity$. By @SmoothnessofMap:Charts[-](ii) $arrow.double$ (i), $F: N arrow RR^m$ is $C^infinity$. \
  (i) $arrow.double$ (iii): Let ${(RR^m, bb(1)_(RR^m))}$ be the atlas on $RR^m$ with a single chart, then by @SmoothnessofMap:Charts[-](i) $arrow.double$ (iii), 
  $
    bb(1)_(RR^m) compose F compose phi.alt^(-1) = F compose phi.alt^(-1): phi.alt(U) arrow RR^m
  $
  is $C^infinity$. \
  (iii) $arrow.double$ (ii): Obvious.
]

#proposition(title: [Smoothness in terms of components], label: <SmoothComponents>)[
  Let $N$ be a manifold. A vector-valued function $F: N arrow RR^m$ is $C^infinity$ if and only if its components functions $F^1, dots.c, F^m: N arrow RR$ are all $C^infinity$.
]
#proof[
  The map $F: N arrow RR^m$ is $C^infinity$. \
  $arrow.r.l.double.long$ For every chart $(U, phi.alt)$ on $N$, $F compose phi.alt^(-1): phi.alt(U) arrow RR^m$ is $C^infinity$. \
  $arrow.r.l.double.long$ For every chart $(U, phi.alt)$ on $N$, the functions $F^i compose phi.alt^(-1): phi.alt(U) arrow RR$ are $C^infinity$. \
  $arrow.r.l.double.long$ The functions $F^i: N arrow RR$ are $C^infinity$.
]

#example[
  (Smoothness of a map to a circle). \
  Prove the map $F: RR arrow S^1, F(t) = (cos t, sin t)$ is $C^infinity$. \
]
#sol[
  Let ${(U_i, phi.alt_i)|i = 1, dots.c, 4}$ be the atlas on $S^1$. On $F^(-1)(U_1)$,
  $
    (phi.alt_1 compose F) (t)= cos t
  $
  is $C^infinity$. Similar computations show that $phi.alt_i compose F$ is $C^infinity$.
]

#proposition(title: [Smoothness of a map in terms of vector-valued functions], label: <SmoothVecValued>)[
  Let $F: N arrow M$ be a continuous map between manifolds of dimensions $n$ and $m$, respectively. The following are equivalent:
  + The map $F: N arrow M$ is $C^infinity$.
  + The manifold $M$ has an atlas such that for every chart $(V, psi) = (V, y^1, dots.c, y^m)$ in the atlas, the vector-valued function
    $
      psi compose F: F^(-1)(V) arrow RR^m
    $
    is $C^infinity$.
  + For every chart $(V, psi) = (V, y^1, dots.c, y^m)$ on $M$, the vector-valued function
    $
      psi compose F: F^(-1)(V) arrow RR^m
    $
    is $C^infinity$.
]
#proof[
  We can prove the proposition as a cycle chain of implications. \
  (ii) $arrow.double$ (i): Let $frak(V)$ be the atlas for $M$ and $frak(U) = {(U, phi.alt)}$ any arbitrary atlas for $N$. Then for each chart $(V, psi) in frak(V)$, the collection
  $
    {(U inter F^(-1)(V), phi.alt|_(U inter F^(-1)(V)))}
  $
  is an atlas for $F^(-1)(V)$. Since $psi compose F$ is $C^infinity$, by @SmoothnessVecValued[-](i) $arrow.double$ (iii), 
  $
    psi compose F compose phi.alt^(-1): phi.alt(U inter F^(-1)(V)) arrow RR^m
  $
  is $C^infinity$. It then follows from @SmoothnessofMap:Charts[-](ii) $arrow.double$ (i) that $F: N arrow M$ is $C^infinity$. \
  (i) $arrow.double$ (iii): Being a coordinate map, $psi$ is $C^infinity$. As a composite of $C^infinity$ maps, $psi compose F$ is $C^infinity$. \
  (iii) $arrow.double$ (ii): Obvious.
]

Combining @SmoothVecValued[-] and @SmoothComponents[-], the smoothness of a map $F: N arrow M$ can be expressed in terms of the smoothness of its components.

#proposition(title: [Smoothness of a map in terms of components])[
  Let $F: N arrow M$ be a continuous map between manifolds of dimensions $n$ and $m$, respectively. The following are equivalent:
  + The map $F: N arrow M$ is $C^infinity$.
  + The manifold $M$ has an atlas such that for every chart $(V, psi) = (V, y^1, dots.c, y^m)$ in the atlas, the components
    $
      y^i compose F: F^(-1)(V) arrow RR
    $
    of $F$ relative to the chart are all $C^infinity$.
  + For every chart $(V, psi) = (V, y^1, dots.c, y^m)$ on $M$, the components
    $
      y^i compose F: F^(-1)(V) arrow RR
    $
    of $F$ relative to the chart are all $C^infinity$.
]

== Examples of Smooth Maps
#example(title: "Smoothness of a projection map")[
  Let $M$ and $N$ be manifolds and 
  $
    pi: M times N &arrow M \
    (p, q) &mapsto p
  $
  the projection to the first factor. Prove that $pi$ is a $C^infinity$ map.
]
#sol[
  Let $(p, q) in M times N$. Suppose $(U, phi.alt) = (U, x^1, dots.c, x^m)$ and $(V, psi) = (V, y^1, dots.c, y^n)$ are charts about $p in M$ and $q in N$, respectively. Then
  $
    (U times V, phi.alt times psi) = (U times V, x^1, dots.c, x^m, y^1, dots.c, y^n)
  $
  is a chart about $(p, q) in M times N$. Then
  $
    (phi.alt compose pi compose (phi.alt times psi)^(-1))(a^1, dots.c, a^m, b^1, dots.c, b^n) = (a^1, dots.c, a^m)
  $
  is a $C^infinity$ map from $phi.alt(U times V) in RR^(m + n)$ to $phi.alt(U) in RR^m$. So $pi$ is $C^infinity$ at $(p, q)$. Since $(p, q)$ is arbitrary, $pi: M times N arrow M$ is $C^infinity$.
]

#example(title: [Smoothness of a map to a Cartesian Product])[
  Let $M_1, M_2$ and $N$ be manifolds of dimensions $m_1, m_2$ and $n$, respectively. Prove that the map
  $
    (f_1, f_2): N arrow M_1 times M_2
  $
  is $C^infinity$ if and only if $f_i: N arrow M_i, i = 1, 2$, are both $C^infinity$.
]
#sol[
  Let $p in N$ and $(U, phi.alt)$ be a chart about $p$. Let $(V_1, psi_1)$ and $(V_2, psi_2)$ be charts about $f_1(p) in M_1$ and $f_2(p) in M_2$, respectively. 
  + Assuming both $f_1$ and $f_2$ are $C^infinity$, then they are both continuous. Then
    $
      (psi_1 times psi_2) compose (f_1, f_2) compose phi.alt^(-1) &= (psi_1 compose f_1 compose phi.alt^(-1), psi_2 compose f_2 compose phi.alt^(-1))\
      &: phi.alt(U inter f_1^(-1)(V_1) inter f_2^(-1)(V_2)) arrow RR^(m_1 + m_2)
    $
    is $C^infinity$. Thus $(f_1, f_2)$ is $C^infinity$ at $p$. Since $p$ is arbitrary, $(f_1, f_2)$ is $C^infinity$ on $N$. \
  + Conversely, if $(f_1, f_2)$ is $C^infinity$, then
    $
      (psi_1 times psi_2) compose (f_1, f_2) compose phi.alt^(-1) &= (psi_1 compose f_1 compose phi.alt^(-1), psi_2 compose f_2 compose phi.alt^(-1))
    $
    is $C^infinity$. Thus, $psi_1 compose f_1 compose phi.alt^(-1)$ and $psi_2 compose f_2 compose phi.alt^(-1)$ are both $C^infinity$, then $f_1$ and $f_2$ are both $C^infinity$ at $p$. Since $p$ is arbitrary, $f_1$ and $f_2$ are both $C^infinity$ on $N$.
]

#example[
  Prove that a $C^infinity$ function $f(x, y)$ on $RR^2$ restricts to a $C^infinity$ function $S^1$.
]
#sol[
  We denote a point on $S^1$ as $p = (a, b)$ and $x, y$ as the standard coordinate functions on $RR^2$, i.e., $x(a, b) = a$ and $y(a, b) = b$. Suppose we can show that $x$ and $y$ restrict to $C^infinity$ functions on $S^1$, then the inclusion map
  $
    i: S^1 &arrow RR^2 \
    p &mapsto (x(p), y(p))
  $
  is $C^infinity$ on $S^1$. Therefore the restriction of $f$ to $S^1$, $f|_(S^1) = f compose i$, is $C^infinity$ on $S^1$. \

  Consider the first function $X$, we use the atlas
  $
    (U_1, phi.alt_1) = ({(x, sqrt(1 - x^2)) | -1 lt x lt 1}, x) \
    (U_2, phi.alt_2) = ({(x, -sqrt(1 - x^2)) | -1 lt x lt 1}, x) \
    (U_3, phi.alt_3) = ({(sqrt(1 - y^2), y) | -1 lt y lt 1}, y) \
    (U_4, phi.alt_4) = ({(-sqrt(1 - y^2), y) | -1 lt y lt 1}, y).
  $
  Since $x$ is a coordinate function on $U_1$ and $U_2$, $x$ is $C^infinity$ on $U_1 union U_2$. The composite
  $
    (x compose phi.alt_3^(-1))(b) = x(sqrt(1 - b^2), b) = sqrt(1 - b^2)
  $
  is $C^infinity$ on $U_3$, thus $x$ is $C^infinity$ on $U_3$. \
  Similarly, the composite
  $
    (x compose phi.alt_4^(-1))(b) = x(-sqrt(1 - b^2), b) = -sqrt(1 - b^2)
  $
  is $C^infinity$ on $U_4$, thus $x$ is $C^infinity$ on $U_4$. \
  Since $x$ is $C^infinity$ on $U_1, U_2, U_3, U_4$, and $S^1 = U_1 union U_2 union U_3 union U_4$, $x$ is $C^infinity$ on $S^1$. \
  The same argument shows that $y$ is $C^infinity$ on $S^1$. \
]

Armed with the definition of a smooth map between manifolds, we can define a Lie group.

#definition[
  A *Lie group* is a $C^infinity$ manifold $G$ having a group structure such that the multiplication map
  $
    mu: G times G arrow G
  $
  and the inverse map
  $
    iota: G arrow G, quad iota(x) = x^(-1),
  $
  are both $C^infinity$.
]

Similarly, A *topological group* is a topological space having a group structure such that the multiplication map and the inverse map are both continuous. Noting that a topological group is required to be a topological space, but not a topological manifold.

#example[
  + The Euclidean space $RR^n$ is a Lie group under addition.
  + The set $C^times$ of nonzero complex numbers is a Lie group under multiplication.
  + The unit circle $S^1$ in $C^times$ is a Lie group under multiplication.
  + The Cartesian product $G_1 times G_2$ of two Lie groups $(G_1, mu_1)$ and $(G_2, mu_2)$ is a Lie group under coordinatewise multiplication $mu_1 times mu_2$.
]

#example(title: [General linear group])[
  The general linear group
  $
    "GL"(n, RR) = {A in [a_(i j)] in RR^(n times n) | det(A) eq.not 0}
  $
  is a manifold, as an open subset of $RR^(n times n)$. Since the $(i, j)$-entry of the product of two matrices $A, B in "GL"(n, RR)$,
  $
    (A times B)_(i j) = sum_(k=1)^n a_(i k) b_(k j),
  $
  is a polynomial in the coordinates of $A$ and $B$, matrix multiplication
  $
    mu: "GL"(n, RR) times "GL"(n, RR) arrow "GL"(n, RR)
  $
  is a $C^infinity$ map. \
  By Cramer's rule from linear algebra, the $(i, j)$-entry of $A^(-1)$ is
  $
    (A^(-1))_(i j) = 1 / (det A) dot (-1)^(i + j) ((j, i)-"minor of" A),
  $
  which is a $C^infinity$ function provided $det A eq.not 0$. Thus, the inverse map
  $
    iota: "GL"(n, RR) arrow "GL"(n, RR)
  $
  is also $C^infinity$. Therefore, $"GL"(n, RR)$ is a Lie group.
]

== Partial Derivatives
#definition[
  On a manifold $M$ of dimension $n$, let $(U, phi.alt) = (U, x^1, dots.c, x^n) = (U, r^1 compose phi.alt, dots.c, r^n compose phi.alt)$ be a chart and $f: M arrow RR^n$ a $C^infinity$ function, where $r^1, dots.c, r^n$ are the standard coordinates on $RR^n$. For $p in U$, the *partial derivative* $(diff f) / (diff x^i)$ of $f$ with respect to $x^i$ at $p$ is defined as
  $
    lr(diff / (diff x^i) |)_p f &:= (diff f) / (diff x^i) (p) \
    &:= (diff (f compose phi.alt^(-1))) / (diff r^i) (phi.alt(p)) \
    &:= lr(diff / (diff r^i) |)_(phi.alt(p)) (f compose phi.alt^(-1)).
  $
  Since $p = phi.alt^(-1)(phi.alt(p))$, this equation can rewritten as
  $
    (diff f) / (diff x^i) (phi.alt^(-1)(phi.alt(p))) = (diff (f compose phi.alt^(-1))) / (diff r^i) (phi.alt(p)).
  $
  Thus, as functions on $phi.alt(U)$,
  $
    (diff f) / (diff x^i) compose phi.alt^(-1) = (diff (f compose phi.alt^(-1))) / (diff r^i).
  $
  The partial derivative $(diff f) / (diff x^i)$ is $C^infinity$ on $U$ because its pullback by $phi.alt^(-1)$, $(diff f) / (diff x^i) compose phi.alt^(-1)$ is $C^infinity$ on $phi.alt(U)$.
]

#proposition[
  Suppose $(U, x^1, dots.c, x^n)$ is a chart on a manifold. Then $(diff x^i) / (diff x^j) = delta^i_j$.
]
#proof[
  At a point $p in U$, by the definition of $diff / (diff x^j)|_p$,
  $
    (diff x^i) / (diff x^j) (p) &= (diff (x^i compose phi.alt^(-1))) / (diff r^j) (phi.alt(p)) \
    &= (diff (r^i compose phi.alt compose phi.alt^(-1))) / (diff r^j) (phi.alt(p)) \
    &= (diff r^i) / (diff r^j) (phi.alt(p)) \
    &= delta^i_j.
  $
]

#definition[
  Let $F: N arrow M$ be a $C^infinity$ map, and let $(U, phi.alt) = (U, x^1, dots.c, x^n)$ and $(V, psi) = (V, y^1, dots.c, y^m)$ be charts on $N$ and $M$ respectively such that $F(U) subset V$. Denote by
  $
    F^i &:= y^i compose F \
    &= r^i compose psi compose F: U arrow RR
  $
  the $i$th component of $F$ in the chart $(V, psi)$. Then the matrix $[(diff F^i) / (diff x^j)]$ is called the *Jacobian matrix* of $F$ relative to the charts $(U, phi.alt)$ and $(V, psi)$. In case $N$ and $M$ have the same dimension, the determinant $det [(diff F^i) / (diff x^j)]$ is called the *Jacobian determinant* of $F$ relative to the two charts. The Jacobian determinant also written as
  $
    (diff (F^1, dots.c, diff F^n)) / (diff (x^1, dots.c, diff x^n)) 
  $
]

When $N$ and $M$ are open subsets of Euclidean spaces and the charts are $(U, r^1, dots.c, r^n)$ and $(V, r^1, dots.c, r^m)$, the Jacobian matrix $[(diff F^i) / (diff r^j)]$, where $F^i = r^i compose F$, is the usual Jacobian matrix from calculus.

#example(title: [Jacobian matrix of a transition map])[
  Let $(U, phi.alt) = (U, x^1, dots.c, x^n)$ and $(V, psi) = (V, y^1, dots.c, y^n)$ be overlapping charts on a manifold $M$. The transition map
  $
    psi compose phi.alt^(-1): phi.alt(U inter V) arrow psi(U inter V)
  $
  is a diffeomorphism of open subsets of $RR^n$. Show that the Jacobian matrix $J(psi compose phi.alt^(-1))$ at $phi.alt(p)$ is the matrix $[(diff y^i) / (diff x^j)]$ of partial derivatives at $p$.
]
#sol[
  By definition, $J(psi compose phi.alt^(-1)) = [(diff (psi thin compose thin phi.alt^(-1))^i) / (diff r^j)]$, where
  $
    (diff (psi compose phi.alt^(-1))^i) / (diff r^j) (phi.alt(p)) &= (diff (r^i compose psi compose phi.alt^(-1))) / (diff r^j) (phi.alt(p)) \
    &= (diff (y^i compose phi.alt^(-1))) / (diff r^j) (phi.alt(p)) \
    &= (diff y^i) / (diff x^j) (p)
  $
]

== The Inverse Function Theorem
#definition(label: <def:LocalInvertible>)[
  A $C^infinity$ map $F: N arrow M$ is *locally invertible* or a *local diffeomorphism* at $p in N$ if $p$ has a neighborhood $U$ on which $F|_U: U arrow F(U)$ is a diffeomorphism.
]

#theorem(title: [Inverse function theorem for $RR^n$])[
  Let $F: W arrow RR^n$ be a $C^infinity$ map defined on an open subset $W subset RR^n$. For any point $p in W$, the map $F$ is locally invertible at $p$ if and only if the Jacobian determinant $det [(diff F^i) / (diff r^j) (p)] eq.not 0$. 
]

Because the inverse function theorem for $RR^n$ is a local result, it easily translates to manifolds.

#theorem(title: [Inverse function theorem for manifolds], label: <InversionFunctionTheorem>)[
  Let $F: N arrow M$ be a $C^infinity$ map between two manifolds of the same dimension, say $n$, and $p in N$. Suppose for some chart $(U, phi.alt) = (U, x^1, dots.c, x^n)$ about $p in N$ and $(V, psi) = (V, y^1, dots.c, y^n)$ about $F(p) in M$, $F(U) subset V$. Set $F^i = y^i compose F$. Then $F$ is locally invertible at $p$ if and only if the Jacobian determinant $det [(diff F^i) / (diff x^j) (p)] eq.not 0$. \
]
#proof[
  $
    [(diff F^i) / (diff x^j) (p)] &= [(diff (y^i compose F)) / (diff x^j) (p)] \
    &= [(diff (r^i compose psi compose F)) / (diff x^j) (p)] \
    &= [(diff (r^i compose psi compose F compose phi.alt^(-1))) / (diff r^j) (phi.alt(p))] \
    &= [(diff (psi compose F compose phi.alt^(-1))^i) / (diff r^j) (phi.alt(p))],
  $
  which is the Jacobian matrix at $phi.alt(p)$ of the map
  $
    psi compose F compose phi.alt^(-1): RR^n supset phi.alt(U) arrow psi(V) subset RR^n
  $
  between two open subsets of $RR^n$. By the inverse function theorem for $RR^n$, 
  $
    det [(diff F^i) / (diff x^j) (p)] = det [(diff (psi compose F compose phi.alt^(-1))^i) / (diff r^j) (phi.alt(p))] eq.not 0
  $
  if and only if $psi compose F compose phi.alt^(-1)$ is locally invertible at $phi.alt(p)$. Since $psi$ and $phi.alt$ are diffeomorphisms, this is equivalent to $F$ being locally invertible at $p$.
]

We usually apply the inverse function theorem in the following form.

#corollary[
  Let $N$ be a manifold of dimension $n$. A set of $n$ smooth functions $F^1, dots.c, F^n$ defined on a coordinate neighborhood $(U, x^1, dots.c, x^n)$ of a point $p in N$ forms a coordinate system about $p$ if and only if the Jacobian determinant $det [(diff F^i) / (diff x^j) (p)] eq.not 0$. \
]
#proof[
  Let $F = (F^1, dots.c, F^n): U arrow RR^n$. Then \
  $det [(diff F^i) / (diff x^j) (p)] eq.not 0$. \
  $arrow.r.l.double.long$ $F: U arrow RR^n$ is locally invertible at $p$. (By @InversionFunctionTheorem[-]) \
  $arrow.r.l.double.long$ There is a neighborhood $W$ of $p in N$ such that $F: W arrow F(W)$ is a diffeomorphism. (By @def:LocalInvertible) \
  $arrow.r.l.double.long$ $(U, F^1, dots.c, F^n)$ is a coordinate chart about $p$ in the differential structure of $N$. (By @DiffeoCoordMap) \
]

#example[
  Find all points in $RR^2$ of which the functions $x^2 + y^2 - 1, y$ can serve as a coordinate system in a neighborhood.
]
#sol[
  Define $F: RR^2 arrow RR^2$ by
  $
    F(x, y) = (x^2 + y^2 - 1, y).
  $
  The map $F$ can serve as a coordinate map in a neighborhood of $p$ if and only if it is a local diffeomorphism at $p$. The Jacobian determinant of $F$ is
  $
    (diff (F^1, F^2)) / (diff (x, y)) &= det mat(
      2x, 2y ;
      0, 1; delim: "[") \
      &= 2x.
  $
  By the inverse function theorem, $F$ is a local diffeomorphism at $p = (x, y)$ if and only if $x eq.not 0$, i.e., $F$ can serve as a coordinate system at any point $p$ not on the $y$-axis.
]

= Quotients
== The Quotient Topology
#definition[
  For an equivalence relation $tilde$ on a set $S$, the *equivalence class* of $x in S$, denoted by $[x]$, is the set of all elements in $S$ equivalent to $x$. An equivalence relation on $S$ partitions $S$ into disjoint equivalence classes. The *quotient* of $S$ by the equivalence relation $tilde$, denoted by $S \/ tilde$, is the set of equivalence classes. There is a natural *projection map* $pi: S arrow S \/ tilde$ defined by
  $
    pi(x) = [x], quad x in S.
  $
]

#definition[
  Assume now that $S$ is a topological space. The *quotient topology* on $S \/ tilde$ is defined as follows: A subset $U subset S \/ tilde$ is open if and only if $pi^(-1)(U)$ is open in $S$. With this topology, $S \/ tilde$ is called the *quotient space* of $S$ by the equivalence relation $tilde$, and the projection map $pi: S arrow S \/ tilde$ is automatically continuous.
]
#proof[
  + $nothing = pi^(-1)(nothing)$ is open in $S$, so $nothing$ is open in $S \/ tilde$; $S = pi^(-1)(S \/ tilde)$ is open in $S$, so $S \/ tilde$ is open in $S \/ tilde$.
  + Let $U_alpha$ be open in $S \/ tilde$, $alpha = 1, 2, dots.c$. Then
    $
      pi^(-1)(limits(union.big)_alpha U_alpha) = limits(union.big)_alpha pi^(-1)(U_alpha)
    $ is open in $S$, so $limits(union.big)_alpha U_alpha$ is open in $S \/ tilde$.
  + Let $U_i$ be open in $S \/ tilde$, $i = 1, dots.c, n$. Then
    $
      pi^(-1)(limits(inter.big)_(i = 1)^n U_i) = limits(inter.big)_(i = 1)^n pi^(-1)(U_i)
    $ is open in $S$, so $limits(inter.big)_(i = 1)^n U_i$ is open in $S \/ tilde$.
]

== Continuity of a Map on a Quotient
Let $tilde$ be an equivalence relation on a topological space $S$ and $S \/ tilde$ the quotient space, with the quotient topology. Suppose a function $f: S arrow Y$ from $S$ to another topological space $Y$ is constant on each equivalence class, i.e., $f(x) = f(y)$ whenever $x tilde y$. Then $f$ induces a function $macron(f): S \/ tilde arrow Y$ defined by
$
  macron(f)([p]) = f(p), quad p in S.
$

#proposition(label: <ContinuityofInducedMap>)[
  The induced map $macron(f): S \/ tilde arrow Y$ is continuous if and only if the map $f: S arrow Y$ is continuous.
]
#proof[
  + $(arrow.double)$ If $macron(f)$ is continuous, then $f = macron(f) compose pi$ is continuous because $pi$ is continuous.
  + $(arrow.double.l)$ Suppose $f$ is continuous. Let $V subset Y$ be open. Then $f^(-1)(V) = pi^(-1)(macron(f)^(-1)(V))$ is open in $S$, so $macron(f)^(-1)(V)$ is open in $S \/ tilde$ by the definition of the quotient topology. Since $V$ is arbitrary, $macron(f)$ is continuous.  
]

This proposition gives a useful criterion for checking whether a function $macron(f)$ on a quotient space $S \/ tilde$ is continuous: simply lift the function $macron(f)$ to $f := macron(f) compose pi$ on $S$ and check whether $f$ is continuous. 

== Identification of a Subset to a Point
#definition[
  Let $A subset S$ be a subset of a topological space $S$, we can define a relation $tilde$ on $S$ by
  $
    x tilde x quad forall x in S 
  $
  and
  $
    x tilde y quad forall x, y in A.
  $
  We say the quotient space $S \/ tilde$ is obetained from $S$ by *identifying $A$ to a point*.
]

#example[
  Let $I = [0, 1]$ and $I \/tilde$ the quotient space obtained from $I$ by identifying the two endpoints ${0, 1}$ to a point. Denote by $S^1$ the unit circle in the complex plane. The function $f: I arrow S^1, f(x) = e^(2 pi i x)$, assumes the same value at $0$ and $1$, and so induces a function $macron(f): I \/tilde arrow S^1$.
]

#proposition[
  The function $macron(f): I \/tilde arrow S^1$ is a homeomorphism.
]

== A Necessary Condition for a Hausdorff Quotient
The quotient construction does not in general preserve the Hausdorff property or second countability. Indeed, since every singleton set in a Hausdorff space is closed, if $pi: S arrow S \/ tilde$ is the projection and the quotient $S \/ tilde$ is Hausdorff, then for any $p in S$, its image ${pi(p)}$ is closed in $S \/ tilde$. By the continuity of $pi$, the inverse image $pi^(-1)({pi(p)}) = [p]$ is closed in $S$. This gives a necessary condition for a quotient space to be Hausdorff.
#proposition[
  If the quotient space $S \/ tilde$ is Hausdorff, then the equivalence class $[p]$ of any point $p in S$ is closed in $S$.
]

#example[
  Define an equivalence relation $tilde$ on $RR$ by identifying the open interval $(0, infinity)$ to a point. Then the quotient space $RR \/ tilde$ is not Hausdorff because the equivalence class $(0, infinity)$ of $tilde$ in $RR$ corresponding to the point $(0, infinity) in RR \/ tilde$ is not closed in $RR$. \
]

== Open Equivalence Relations
#definition[
  A map $f: X arrow Y$ of topological spaces is *open* if for every open set $U subset X$, the image $f(U)$ is open in $Y$. \
]

#definition[
  An equivalence relation $tilde$ on a topological space $S$ is *open* if the projection map $pi: S arrow S \/ tilde$ is open. \
  Equivalently, $tilde$ is open if for every open set $U subset S$, the set
  $
    pi^(-1)(pi(U)) = union.big_(x in U) [x]
  $
  is open in $S$.
]

#example[
  The projection map ro a quotient space is in general not open. For example, let $tilde$ be the equivalence relation on the real line $RR$ that identifies the two points $1$ and $-1$ to a point. The projection map $pi: RR arrow RR \/ tilde$ is not open.
]
#sol[
  Let $V = (-2, 0) subset RR$ be an open set in $RR$. Then
  $
    pi^(-1)(pi(V)) = (-2, 0) union {1},
  $
  which is not open in $RR$. Thus, $pi$ is not open.
]

#definition[
  Given an equivalence relation $tilde$ on $S$, the *graph* of $tilde$ is the subset $R subset S times S$ defined by
  $
    R = {(x, y) in S times S | x tilde y}
  $
]

#theorem(label: <HausdorffonQuotient>)[
  Suppose $tilde$ is an open equivalence relation on a topological space $S$. Then the quotient space $S \/ tilde$ is Hausdorff if and only if the graph $R$ of $tilde$ is closed in $S times S$.
]
#proof[
  There is a sequence of equivalent statements: \
  $R$ is closed in $S times S$ \
  $arrow.r.l.double.long$ $(S times S) - R$ is open in $S times S$ \
  $arrow.r.l.double.long$ For every $(x, y) in S times S$, there is a basic open set $U times V$ containing $(x, y)$ such that $(U times V) inter R = nothing$ \
  $arrow.r.l.double.long$ For every pair $x tilde.not y$ in $S$, there exists neighborhoods $U$ of $x$ and $V$ of $y$ such that no element of $U$ is equivalent to an element of $V$ \
  $arrow.r.l.double.long$ For any two points $[x] eq.not [y]$ in $S \/ tilde$, there exists neighborhoods $U$ of $x$ and $V$ of $y$ in $S$ such that $pi(U) inter pi(V) = nothing$ in $S \/ tilde$ \
  Since $pi$ is open, $pi(U)$ and $pi(V)$ are disjoint open sets in $S \/ tilde$ containing $[x]$ and $[y]$, respectively. Therefore, $S \/ tilde$ is Hausdorff. \
  Conversely, suppose $S \/ tilde$ is Hausdorff. Let $[x] eq.not [y]$ in $S \/ tilde$. Then there exist disjoint open sets $A, B subset S \/ tilde$ such that $[x] in A$ and $[y] in B$. By the surjectivity of $pi$, we have $A = pi(pi^(-1)(A))$ and $B = pi(pi^(-1)(B))$. Let $U = pi^(-1)(A)$ and $V = pi^(-1)(B)$. Then $x in U, y in V$, and $A = pi(U), B = pi(V)$ are disjoint open sets in $S \/ tilde$.
]

If the equivalence relation $tilde$ is equality, then the quotient space $S \/ tilde$ is $S$ itself and the graph $R$ of $tilde$ is simply the diagonal
$
  Delta = {(x, x) in S times S},
$
where @HausdorffonQuotient becomes the following well-known characterization of a Hausdorff space by its diagonal.
#corollary[
  A topological space $S$ is Hausdorff if and only if the diagonal $Delta = {(x, x) | x in S}$ is closed in $S times S$.
]

#theorem[
  Let $tilde$ be an open equivalence relation on a topological space $S$ with projection $pi: S arrow S \/ tilde$. If $cal(B) = {B_alpha}$ is a basis for $S$, then its image ${pi(B_alpha)}$ under $pi$ is a basis for $S \/ tilde$.
]
#proof[
  Since $pi$ is an open map, ${pi(B_alpha)}$ is a collection of open sets in $S \/ tilde$. Let $W$ be an open set in $S \/ tilde$ and $[x] in W, x in S$. Then $x in pi^(-1)(W)$. Since $pi^(-1)(W)$ is open in $S$, there exists a basic open set $B in cal(B)$ such that
  $
    x in B subset pi^(-1)(W).
  $
  Then
  $
    [x] = pi(x) in pi(B) subset W,
  $
  which proves that ${pi(B_alpha)}$ is a basis for $S \/ tilde$.
]

#corollary[
  If $tilde$ is an open equivalence relation on a second-countable space $S$, then the quotient space $S \/ tilde$ is second countable.
]

== Real Projective Space
#definition[
  The *real projective space* $RR P^n$ is the quotient space of $RR^(n + 1) - {0}$ by the equivalence relation $tilde$ defined by
  $
    x tilde y quad arrow.r.l.double.long quad y = t x "for some nonzero real number" t.
  $
  The *homogeneous coordinates* of a point $(a^0, dots.c, a^n) in RR^(n + 1) - {0}$ are the equivalence class $[a^0, dots.c, a^n]$. \
]

Geometrically, two nonzero points in $RR^(n + 1)$ are equivalent if and only if they lie on the same line through the origin, so $RR P^n$ can be interpreted as the set of all lines through the origin in $RR^(n + 1)$. Each line through the origin in $RR^(n + 1)$ meets the unit sphere $S^n$ in a pair of antipodal points, and conversely, a pair of antipodal points on $S^n$ determines a unique line through the origin. This suggests that we define an equivalence relation $tilde$ on $S^n$ by identifying antipodal points:
$
  x tilde y quad arrow.r.l.double.long quad x = plus.minus y, quad x, y in S^n,
$
which gives a bijection $RR P^n arrow.l.r S^n \/ tilde$.

#example(title: [Real projective space as a quotient of a sphere])[
  For $x = (x^1, dots.c, x^n) in RR^n$, let $norm(x) = sqrt(sum_i (x^i)^2)$ be the module of $x$. Prove that the map $f: RR^(n + 1) - {0} arrow S^n$ given by
  $
    f(x) = x / norm(x)
  $
  introduces a homeomorphism $macron(f): RR P^n arrow S^n \/ tilde$.(Hint: Find an inverse map
  $
    macron(g): S^n \/ tilde arrow RR P^n
  $
  and show that both $macron(f)$ and $macron(g)$ are continuous.)
]
#sol[
  Let $attach(tilde, br: 1)$ be the equivalence relation on $RR^(n + 1) - {0}$ defined by
  $
    x tilde y quad arrow.r.l.double.long quad y = t x "for some nonzero real number" t,
  $
  and the projection map $pi_1: RR^(n + 1) - {0} arrow RR P^n$. \
  Let $attach(tilde, br: 2)$ be the equivalence relation on $S^n$ defined by
  $
    x tilde y quad arrow.r.l.double.long quad x = plus.minus y, quad x, y in S^n,
  $
  and the projection map $pi_2: S^n arrow S^n \/ attach(tilde, br: 2)$. \
  + $macron(f)$ is continuous. \
    For $x attach(tilde, br: 1) y$ in $RR^(n + 1) - {0}$, i.e., $y = t x$ for some nonzero real number $t$, we have
    $
      f(y) &= y / norm(y) \
      &= (t x) / norm(t x) \
      &= (t x) / (abs(t) norm(x)) \
      &= "sgn(t)" f(x) \
      &= plus.minus f(x),
    $
    which means $f(y) attach(tilde, br: 2) f(x)$ in $S^n$. Then the map
    $
      pi_2 compose f: RR^(n + 1) - {0} arrow S^n \/ attach(tilde, br: 2)
    $
    is constant on the equivalence classes of $attach(tilde, br: 1)$ of $RR^(n + 1) - {0}$, so it induces a map
    $
      macron(f): RR P^n arrow S^n \/ attach(tilde, br: 2), quad macron(f)([x]_attach(tilde, br: 1)) = pi_2 compose f(x),
    $
    which is continuous since $f$ and $pi_2$ are continuous. 
  + $macron(g)$ is continuous. \
    For $q in S^n subset RR^(n + 1) - {0}$ with inclusion map
    $
      i: S^n arrow RR^(n + 1) - {0}, quad i(q) = q,
    $
    define
    $
      macron(g): S^n \/ attach(tilde, br: 2) arrow RR P^n, quad macron(g)([q]_attach(tilde, br: 2)) = [q]_attach(tilde, br: 1).
    $
    For $p attach(tilde, br: 2) q$ in $S^n$, i.e., $p = plus.minus q$, we have
    $
      macron(g)([p]_attach(tilde, br: 2)) &= [p]_attach(tilde, br: 1) \
      &= [plus.minus q]_attach(tilde, br: 1) \
      &= [q]_attach(tilde, br: 1),
    $
    so $macron(g)$ is well defined.
    Since
    $
      macron(g) compose pi_2: S^n arrow RR P^n, quad macron(g) compose pi_2(q) = [q]_attach(tilde, br: 1) = pi_1 compose i(q),
    $
    then
    $
      macron(g) compose pi_2 = pi_1 compose i,
    $
    which shows that $macron(g)$ is continuous.
  + $macron(f)$ is bijective
    + $macron(f)$ is surjective. \
      For any$[q]_attach(tilde, br: 2)$ in $S^n \/ attach(tilde, br: 2)$, a presentative $q in S^n subset RR^(n + 1) - {0}$,
      $
        macron(f)([q]_attach(tilde, br: 1)) &= pi_2 compose f(q) \
        &= [q / norm(q)]_attach(tilde, br: 2) \
        &= [q]_attach(tilde, br: 2).
      $
    + $macron(f)$ is injective. \
      Suppose
      $
        macron(f)([x]_attach(tilde, br: 1)) = macron(f)([y]_attach(tilde, br: 1)), quad x, y in RR^(n + 1) - {0}.
      $
      Then
      $
        [x / norm(x)]_attach(tilde, br: 2) &= [y / norm(y)]_attach(tilde, br: 2) \
        y / norm(y) &= plus.minus x / norm(x) \
        y &= plus.minus norm(y) / norm(x) x,
      $
      which means $y attach(tilde, br: 1) x$ in $RR^(n + 1) - {0}$, i.e., $[y]_attach(tilde, br: 1) = [x]_attach(tilde, br: 1)$.
  + $macron(g)$ is bijective
    + $macron(g)$ is surjective. \
      For any $[x]_attach(tilde, br: 1)$ in $RR P^n$, a presentative $x in RR^(n + 1) - {0}$,
      $
        macron(g)([x / norm(x)]_attach(tilde, br: 2)) &= [x / norm(x)]_attach(tilde, br: 1) \
        &= [x]_attach(tilde, br: 1).
      $
    + $macron(g)$ is injective. \
      Suppose
      $
        macron(g)([x]_attach(tilde, br: 2)) = macron(g)([y]_attach(tilde, br: 2)), quad x, y in S^n.
      $
      Then
      $
        [x]_attach(tilde, br: 1) &= [y]_attach(tilde, br: 1) \
        x &= t y "for some nonzero real number" t,
      $
      which means $x = plus.minus y$, since $x, y in S^n$. Thus, $[x]_attach(tilde, br: 2) = [y]_attach(tilde, br: 2)$.
  + $macron(f)$ and $macron(g)$ are mutually inverse maps. 
    + For $[x]_attach(tilde, br: 1) in RR P^n$, 
      $
        macron(g) compose macron(f)([x]_attach(tilde, br: 1)) &= macron(g)(pi_2 compose f(x)) \
        &= macron(g)([x / norm(x)]_attach(tilde, br: 2)) \
        &= [x / norm(x)]_attach(tilde, br: 1) \
        &= [x]_attach(tilde, br: 1).
      $
    + For $[q]_attach(tilde, br: 2) in S^n \/ attach(tilde, br: 2)$,
      $
        macron(f) compose macron(g)([q]_attach(tilde, br: 2)) &= macron(f)([q]_attach(tilde, br: 1)) \
        &= [q / norm(q)]_attach(tilde, br: 2) \
        &= [q]_attach(tilde, br: 2).
      $
]

#example(title: [The real projective line $RR P^1$])[
  Each line through the origin in $RR^2$ meets the unit circle $S^1$ in a pair of antipodal points. As we've proved, $RR P^n$ is homeomorphic to $S^n \/ tilde$, which is in turn homeomorphic to the closed upper semicircle with the two endpoints identified. Thus, $RR P^1$ is homeomorphic to the circle $S^1$.
]

#example(title: [The real projective plane $RR P^2$])[
  We've shown that there is a homeomorphism
  $
    RR P^2 tilde.eq S^2 \/ tilde.
  $
  Let $H^2$ be the closed upper hemisphere
  $
    H^2 = {(x, y, z) in RR^3 | x^2 + y^2 + z^2 = 1, z gt.eq 0}.
  $
  and let $D^2$ be the closed disk
  $
    D^2 = {(x, y) in RR^2 | x^2 + y^2 lt.eq 1}.
  $
  These two spaces are homeomorphic to each other via the continuous map
  $
    phi: H^2 &arrow D^2, \
    phi(x, y, z) &= (x, y),
  $
  and its inverse
  $
    psi: D^2 &arrow H^2, \
    psi(x, y) &= (x, y, sqrt(1 - x^2 - y^2)).
  $
  On $H^2$, define an equivalence relation $tilde$ by identifying the antipodal points on the equator:
  $
    (x, y, 0) tilde (-x, -y, 0), quad x^2 + y^2 = 1.
  $
  On $D^2$, define an equivalence relation $tilde$ by identifying the antipodal points on the boundary:
  $
    (x, y) tilde (-x, -y), quad x^2 + y^2 = 1.
  $
  Then $phi$ and $psi$ induce homeomorphisms
  $
    macron(phi): H^2 \/ tilde arrow D^2 \/ tilde, quad macron(psi): D^2 \/ tilde arrow H^2 \/ tilde.
  $
  There is a homeomorphism between $S^2 \/ tilde$ and $H^2 \/ tilde$. \
  In summary, there is a sequence of homeomorphisms
  $
    RR P^2 arrow^tilde S^2 \/ tilde arrow^tilde H^2 \/ tilde arrow^tilde D^2 \/ tilde.
  $
]

#proposition[
  The equivalence relation $tilde$ on $RR^(n + 1) - {0}$ in the definition of $RR P^n$ is open.
]
#proof[
  For any open set $U subset RR^(n + 1) - {0}$, the image $pi(U)$ is open in $RR P^n$ if and only if
  $
    pi^(-1)(pi(U)) = union.big_(t in RR^times) t U
  $
  is open in $RR^(n + 1) - {0}$. Since $t U$ is open in $RR^(n + 1) - {0}$ for any nonzero real number $t$, the union $union.big_(t in RR^times) t U$ is open in $RR^(n + 1) - {0}$. Thus, $tilde$ is open.
]

#corollary[
  The real projective space $RR P^n$ is second countable.
]

#proposition[
  The real projective space $RR P^n$ is Hausdorff.
]
#proof[
  Let $S = RR^(n + 1) - {0}$ and consider the set
  $
    R = {(x, y) in S times S | y = t x "for some" t in RR^times}.
  $
  As $R$ is closed in $S times S$, since $tilde$ is open, the quotient space $RR P^n$ is Hausdorff by @HausdorffonQuotient.
]

== The Standard $C^infinity$ Atlas on a Real Projective Space
Let $[a^0, dots.c, a^n]$ be homogeneous coordinates on $RR P^n$. Although $a^0$ is not a well-defined function on $RR P^n$, the condition $a^0 eq.not 0$ is independent of the choice of a representative for $[a^0, dots.c, a^n]$. Hence, the condition $a^0 eq.not 0$ makes sense on $RR P^n$, and we may define
$
  U_0 := { [a^0, dots.c, a^n] in RR P^n | a^0 eq.not 0 }.
$
Similarly, for each $i = 1, dots.c, n$, we define
$
  U_i := { [a^0, dots.c, a^n] in RR P^n | a^i eq.not 0 }.
$
Define
$
  phi.alt_0: U_0 &arrow RR^n \
  [a^0, dots.c, a^n] &mapsto (a^1 / a^0, dots.c, a^n / a^0),
$
which has a continuous inverse
$
  (b^1, dots.c, b^n) &mapsto [1, b^1, dots.c, b^n]
$
and is therefore a homeomorphism. Similarly, there are homeomorphisms
$
  phi.alt_i: U_i &arrow RR^n \
  [a^0, dots.c, a^n] &mapsto (a^0 / a^i, dots.c, hat(a^i) / a^i, dots.c, a^n / a^i),
$
where the caret sign $\^$ over $a^i / a^i$ means that entry is to be omitted. This proves that $RR P^n$ is locally Euclidean with $(U_i, phi.alt_i)$ as charts.
On the intersection $U_0 inter U_1$, there are two coordinate systems
#figure(
  diagram({
  let (p, a, b) = ((0, -1), (-1, 0), (1, 0))
  node(p, $[a^0, a^1, a^2, dots.c, a^n]$)
  node(a, $(a^1 / a^0, a^2 / a^0, dots.c, a^n / a^0)$)
  node(b, $(a^0 / a^1, a^2 / a^1, dots.c, a^n / a^1)$)
  edge(p, a, $phi.alt_0$, "->")
  edge(p, b, $phi.alt_1$, "->")
}))
We will refer the coordinate functions on $U_0$ as $x^1, dots.c, x^n$, and $y^1, dots.c, y^n$ on $U_1$. On $U_0$,
$
  x^i = a^i / a^0, quad i = 1, dots.c, n,
$ 
and on $U_1$,
$
  y^1 = a^0 / a^1, quad y^i = a^i / a^1, i = 2, dots.c, n.
$
Then on $U_0 inter U_1$, 
$
  y^1 = 1 / x^1, quad y^i = x^i / x^1, i = 2, dots.c, n,
$
so
$
  phi.alt_1 compose phi.alt_0^(-1)(x) = (1 / x^1, x^2 / x^1, dots.c, x^n / x^1),
$
and
$
  phi.alt_0 compose phi.alt_1^(-1)(y) = (1 / y^1, y^2 / y^1, dots.c, y^n / y^1),
$
which are both smooth because $x^1 eq.not 0$ on $phi.alt_0(U_0 inter U_1)$ and $y^1 eq.not 0$ on $phi.alt_1(U_0 inter U_1)$, then $(U_0, phi.alt_0)$ and $(U_1, phi.alt_1)$ are compatible. On any other intersection $U_i inter U_j$, an analogous formula holds. Therefore, the collection${(U_i, phi.alt_i)}_(i = 0, dots.c, n)$ is a $C^infinity$ atlas for $RR P^n$, called the *standard atlas*. This concludes the proof that $RR P^n$ is a manifold of dimension $n$.
