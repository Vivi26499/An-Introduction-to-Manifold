#import "../Assignment.typ": *
#import "@preview/cetz:0.3.4"
#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  chapter: 2,
)
#counter(heading).update(4)
#section[Manifolds]

#prob[
  Let $A$ and $B$ be points on the real line $RR$. Consider the set $S = (RR - {0}) union {A, B}$.
  #figure(
  cetz.canvas({
    import cetz.draw: *
    circle((0, 0.5), radius: 2pt, fill: black, name: "A")
    content("A", [A], anchor: "south-west")
    circle((0, -0.5), radius: 2pt, fill: black, name: "B")
    content("B", [B], anchor: "north-west")
    line((0.1, 0), (3, 0))
    line((-3, 0), (-0.1, 0))
  }),
  caption: [Real line with two origins],
  )
  For any two positive real numbers $c, d$, define
  $
    I_A (-c, d) = (-c, 0) union {A} union (0, d)
  $
  
  Similarly for $I_B (-c, d)$, with $B$ in place of $A$. Define a topology on $S$ as follows: on $(RR - {0})$, use the subspace topology inherited from $RR$, with open intervals as a basis. A basis of neighborhoods at $A$ is the collection ${I_A (-c, d) | c, d > 0}$; similarly, a basis of neighborhoods at $B$ is ${I_B (-c, d) | c, d > 0}$.
  
  + Prove that the map $h: I_A (-c, d) -> (-c, d)$ defined by 
    $ 
      h(x) &= x quad "for" x in (-c, 0) union (0, d), \
      h(A) &= 0 
    $
    is a homeomorphism.
  
  + Prove that $S$ is locally Euclidean and second countable, but not Hausdorff.
]
#sol[
  + To show that $h$ is a homeomorphism, we need to show that it is continuous and has a continuous inverse. \
    + $h$ is injective. \
      Let $x, y in I_A (-c, d)$ such that $h(x) = h(y)$. There are two cases:
      - $h(x) = h(y) = 0$, then $x = y = A$
      - $h(x) = h(y) eq.not 0$, then $h(x) = x$ and $h(y) = y$, so $x = y$.
    + $h$ is surjective. \
      Let $y in (-c, d)$. There are two cases:
      - $y eq.not 0$, then $y in I_A (-c, d)$ and $h(y) = y$.
      - $y = 0$, then $h(A) = 0 = y$.
    + $h$ is continuous. \
      Let $(x, y) subset.eq (-c, d)$ be an open interval. There are two cases:
      - $0 in (x, y)$, then $h^(-1)((x, y)) = I_A (x, y) subset.eq I_A (-c, d)$ is open.
      - $0 in.not (x, y)$, then $h^(-1)((x, y)) = (x, y) subset.eq I_A (-c, d)$ is open.
    + $h^(-1)$ is continuous. \
      There are two cases:
      - $A in (x, y)$, then $h(I_A (x, y)) = (x, y) in (-c, d)$ is open.
      - $A in.not (x, y)$, then $h((x, y)) = (x, y) in (-c, d)$ is open.
    Therefore, $h$ is a homeomorphism.
  + + $S$ is locally Euclidean. \
    From (a), we know that for any $x in S$, there is a neighborhood $U$ of $x$ such that $U$ is homeomorphic to an open subset of $RR$ with $h$ as the homeomorphism. 
    + $S$ is second countable. \
    + $S$ is not Hausdorff. 
      Consider the points $A$ and $B$. For any open set $U$ containing $A$, we have $U = I_A (-a_1, a_2)$ for some $a_1, a_2 > 0$. Similarly, for any open set $V$ containing $B$, we have $V = I_B (-b_1, b_2)$ for some $b_1, b_2 > 0$. Suppose $U inter V = nothing$. Let $c_1 = max(a_1, b_1)$ and $c_2 = min(a_2, b_2)$. Then $U inter V = (c_1, 0) union (0, c_2)$, which is not empty. Therefore, $S$ is not Hausdorff.
]

#prob[
  A fundamental theorem of topology, the theorem on invariance of dimension, states that if two nonempty open sets $U subset.eq RR^n$ and $V subset.eq RR^m$ are homeomorphic, then $n = m$. Use the idea of Example 5.4 as well as the theorem on invariance of dimension to
  prove that the sphere with a hair in $RR^3$ is not locally Euclidean at $q$. Hence it
  cannot be a topological manifold.
  #figure(
    cetz.canvas({
      import cetz.draw: *
      circle((0, 0), radius: 1, stroke: black)
      circle((0.6, 0.8), radius: 0.1, fill: black, name: "q")
      arc((1,0), start: 0deg, delta: 180deg, radius: (1, 0.45), stroke: (dash: "dashed"))
      arc((1,0), start: 0deg, delta: -180deg, radius: (1, 0.45))
      content((0.5, 1), [q], anchor: "south-east")
      arc-through("q", (1, 1), (2, 0.8))
      
    }),
    caption: [A sphere with a hair.]
  )
]
#sol[
  Suppose the sphere with a hair is locally Euclidean of dimension $n$ at $q$. Then there is a neighborhood $U$ of $q$ such that $U$ is homeomorphic to an open ball $B = B(0, epsilon) subset.eq RR^n$ with $q$ mapping to $0$. The homeomorphism $U arrow B$ restricts to a homeomorphism $U without {q} arrow B without {0}$. Since $B without {0}$ is either connected if $n gt.eq 2$ or has two connected components if $n = 1$ and $U without {q}$ has two connected components, $n$ must be $1$, i.e., $U$ is homeomorphic to an open interval $U subset.eq RR$. However, a neighborhood on the sphere has dimension $2$. By invarience of dimension, the sphere with a hair cannot be locally Euclidean at $q$.
]

#prob[
  Let $S^2$ be the unit sphere
  $
    x^2 + y^2 + z^2 = 1
  $
  in $RR^3$. Define in $S^2$ the six charts corresponding to the six hemispheres—the front, rear, right,
  left, upper, and lower hemispheres:
  $
    U_1 &= {(x,y,z) in S^2 | x > 0}, quad phi.alt_1(x,y,z) = (y,z), \
    U_2 &= {(x,y,z) in S^2 | x < 0}, quad phi.alt_2(x,y,z) = (y,z), \
    U_3 &= {(x,y,z) in S^2 | y > 0}, quad phi.alt_3(x,y,z) = (x,z), \
    U_4 &= {(x,y,z) in S^2 | y < 0}, quad phi.alt_4(x,y,z) = (x,z), \
    U_5 &= {(x,y,z) in S^2 | z > 0}, quad phi.alt_5(x,y,z) = (x,y), \
    U_6 &= {(x,y,z) in S^2 | z < 0}, quad phi.alt_6(x,y,z) = (x,y).
  $
  Describe the domain $phi.alt_4(U_(14))$ of $phi.alt_1 compose phi.alt_4^(-1)$ and show that $phi.alt_1 compose phi.alt_4^(-1)$ is $C^infinity$ on $phi.alt_4(U_(14))$. Do the same for $phi.alt_6 compose phi.alt_1^(-1)$.
]
#sol[
  As $U_(14) = U_1 inter U_4$, $phi.alt_4(U_(14)) = {(x, z) | x > 0, x^2 + z^2 lt 1})$, and the transition map $phi.alt_1 compose phi.alt_4^(-1)$ is given by
  $
    phi.alt_1 compose phi.alt_4^(-1)(x, z) &= phi.alt_1(x, -sqrt(1 - x^2 - z^2), z) \
    &= (-sqrt(1 - x^2 - z^2), z),
  $
  which is $C^infinity$ on $phi.alt_4(U_(14))$.
]

#prob[
  Let ${(U_alpha, phi.alt_alpha)}$ be the maximal atlas on a manifold $M$. For any open set $U$ in $M$ and a point 
  $p in U$, prove the existence of a coordinate open set $U_alpha$ such that $p in U_alpha subset.eq U$.
]
#sol[
  Let $U_beta$ be a coordinate open set such that $p in U_beta subset.eq U$. Then $U_alpha = U_beta inter U$ is a coordinate open set such that $p in U_alpha subset.eq U$.
]

#section[Smooth Maps on a Manifold]

#prob[
  Let $RR$ be the real line with the differentiable structure given by the maximal atlas of the chart
  $(RR, phi.alt = 1 : RR -> RR)$, and let $RR'$ be the real line with the differentiable structure given by the
  maximal atlas of the chart $(RR, psi : RR -> RR)$, where $psi(x) = x^(1/3)$.

  + Show that these two differentiable structures are distinct.
  + Show that there is a diffeomorphism between $RR$ and $RR'$. (Hint: The identity map $RR -> RR$
    is not the desired diffeomorphism; in fact, this map is not smooth.)
]
#sol[
  + Suppose that $RR$ and $RR'$ have the same differentiable structure. Then $F: RR arrow RR'$ must be the identity map and $psi compose F compose phi.alt$ must be a diffeomorphism. However, for $x in RR$, 
    $
      psi compose F compose phi.alt^(-1)(x) = psi(x) = x^(1/3), 
    $
    is not $C^infinity$ at $0$. Therefore, $RR$ and $RR'$ have distinct differentiable structures.
  + Let $F: RR -> RR'$ be the map defined by $F(x) = x^3$. For $x in RR$, we have
    $
      psi compose F compose phi.alt^(-1)(x) = psi(x^3) = (x^3)^(1/3) = x,
    $
    is a diffeomorphism. Therefore, $F$ is a diffeomorphism between $RR$ and $RR'$.
]

#prob[
  Let $M$ and $N$ be manifolds and let $q_0$ be a point in $N$. Prove that the inclusion map $i_(q_0) : M ->
  M times N$, $i_(q_0) (p) = (p, q_0)$, is $C^infinity$.
]
#sol[
  Let $(U_alpha, phi.alt_alpha)$ and $(V_i, psi_i)$ be a chart of $M$ and $N$, respectively, then $(U_alpha times V_i, phi.alt_alpha times psi_i)$ is a chart of $M times N$. To show that $i_(q_0)$ is $C^infinity$, we have the map
  $
    (phi.alt_alpha times psi_i) compose i_(q_0) compose phi.alt_beta^(-1) (x) &= (phi.alt_alpha times psi_i)(phi.alt_alpha^(-1), q_0) \
    &= (phi.alt_alpha compose phi.alt_beta^(-1)(x), psi_i (q_0)).
  $
  As $phi.alt_alpha$ and $phi.alt_beta$ are compatible and $psi_i (q_0)$ is a constant, the map is $C^infinity$. Therefore, $i_(q_0)$ is $C^infinity$.
]

#prob[
  Let $V$ be a finite-dimensional vector space over $RR$, and $"GL"(V)$ the group of all linear automorphisms of $V$. Relative to an ordered basis $e = (e_1, ..., e_n)$ for $V$, a linear automorphism
  $L in "GL"(V)$ is represented by a matrix $[a^i_j]$ defined by
  $
    L(e_j) = sum_i a^i_j e_i.
  $
  The map
  $
    phi.alt_e : "GL"(V) -> "GL"(n, RR), \
    L |-> [a^i_j],
  $

  is a bijection with an open subset of $RR^(n times n)$ that makes $"GL"(V)$ into a $C^infinity$ manifold, which we
  denote temporarily by $"GL"(V)_e$. If $"GL"(V)_u$ is the manifold structure induced from another
  ordered basis $u = (u_1, ..., u_n)$ for $V$, show that $"GL"(V)_e$ is the same as $"GL"(V)_u$.
]
#sol[
  
]

#prob[
  Find all points in $RR^3$ of which the functions $x, x^2 + y^2 + z^2 - 1, z$ can serve as a local coordinates system in a neighborhood.
]
#sol[
  For$(x, y, z) in RR^3$, define $F: RR^3 arrow RR^3$ by
  $
    F(x, y, z) = (x, x^2 + y^2 + z^2 - 1, z).
  $
  The Jacobian determinant of $F$ is
  $
    (diff (F^1, F^2, F^3)) / (diff (x, y, z)) &= det mat(
      1, 0, 0;
      2x, 2y, 2z;
      0, 0, 1; delim: "["
    ) \
    &= 2y.
  $
  By the inverse function theorem, $F$ is a local coordinate system at $(x, y, z)$ if and only if $2y eq.not 0$. Therefore, the points in $RR^3$ of which the functions $x, x^2 + y^2 + z^2 - 1, z$ can serve as a local coordinates system in a neighborhood are all points except the $x-z$ plane.
]

#section[Quotients]

#prob[
  Let $f: X -> Y$ be a map of sets, and let $B subset Y$. Prove that $f(f^(-1)(B)) = B inter f(X)$. Therefore, if $f$ is surjective, then $f(f^(-1)(B)) = B$.
]
#sol[
  + For $x in f(f^(-1)(B))$, there exists $y in f^(-1) (B)$ such that $x = f(y) in f(X)$ and $y in f^(-1)(B)$, so $f(y) in B$. Therefore, $x in B inter f(X)$.
  + For $x in B inter f(X)$, there exists $y in X$ such that $x = f(y) in B$, so $y in f^(-1)(B)$. Therefore, $x in f(f^(-1)(B))$.
  Therefore, $f(f^(-1)(B)) = B inter f(X)$. \
  If $f$ is surjective, then $f(f^(-1)(B)) = B inter f(X) = B inter Y = B$.
]

#prob[
  Let $H^2$ be the closed upper hemisphere in the unit sphere $S^2$, and let $i: H^2 -> S^2$ be the inclusion map. In the notation of Example 7.13, prove that the induced map $f: H^2 \/ tilde -> S^2 \/ tilde$ is a homeomorphism. (Hint: Imitate Proposition 7.3.)
]
#sol[
  
]

#prob[
  Deduce Theorem 7.7 from Corollary 7.8. (Hint: To prove that if $S \/ tilde$ is Hausdorff, then the graph $R$ of $tilde$ is closed in $S times S$, use the continuity of the projection map $pi: S -> S \/ tilde$. To prove the reverse implication, use the openness of $pi$.)
]
#sol[
  Suppose $tilde$ is an open equivalence relation on $S$, then the projection map $pi: S -> S \/ tilde$ is open. Then \
  $S \/ tilde$ is Hausdorff. \
  $arrow.r.l.double.long$ The diagonal $Delta = {([x],[x]) in (S \/ tilde) times (S \/ tilde)}$ is closed in $(S \/ tilde) times (S \/ tilde)$, \
  $arrow.r.l.double.long$ $(pi^(-1) times pi^(-1))Delta = {(x, y) | x tilde y} = R$ is closed in $S times S$. \
]

#prob[
  Let $S^n$ be the unit sphere centered at the origin in $RR^(n+1)$. Define an equivalence relation $tilde$ on $S^n$ by identifying antipodal points:
  $
    x tilde y <==> x = plus.minus y, quad x, y in S^n.
  $

  + Show that $tilde$ is an open equivalence relation.
  + Apply Theorem 7.7 and Corollary 7.8 to prove that the quotient space $S^n \/ tilde$ is Hausdorff, without making use of the homeomorphism $RR P^n tilde.eq S^n \/ tilde$.
]
#sol[
  + Let $U subset S^n$ be an open set. Then $pi^(-1)(pi(U)) = U union a(U)$, where $a: S^n -> S^n, a(x) = -x$ is the antipodal map. Since $a$ is a homeomorphism, $a(U)$ is open. Therefore, $pi^(-1)(pi(U))$ is open as a union of two open sets, then $pi(U)$ is open by the definition of the quotient topology. Thus, $pi$ is an open map, i.e., $tilde$ is an open equivalence relation.
  + The graph $R$ of $tilde$ is
    $
      R &= {(x, y) | x tilde y} \
      &= {(x, x) in S^n times S^n} union {(x, -x) in S^n times S^n} \
      &= Delta union (bb(1) times a) Delta.
    $
    Since $S^n$ is Hausdorff, the diagonal $Delta$ is closed in $S^n times S^n$. Since $bb(1) times a: S^n times S^n -> S^n times S^n, (bb(1) times a)(x, y) = (x, -y)$ is a homeomorphism, $(bb(1) times a)(Delta)$ is closed in $S^n times S^n$. Therefore, $R$ is closed in $S^n times S^n$ as a union of two closed sets, then $S^n \/ tilde$ is Hausdorff.
]

#prob[
  Suppose a right action of a topological group $G$ on a topological space $S$ is continuous; this simply means that the map $S times G -> S$ describing the action is continuous. Define two points $x, y$ of $S$ to be equivalent if they are in the same orbit; i.e., there is an element $g in G$ such that $y = x g$. Let $S \/ G$ be the quotient space; it is called the orbit space of the action. Prove that the projection map $pi: S -> S \/ G$ is an open map. (This problem generalizes Proposition 7.14, in which $G = RR^times$ = $RR - {0}$ and $S = RR^(n+1) - {0}$. Because $RR^times$ is commutative, a left $RR^times$-action becomes a right $RR^times$-action if scalar multiplication is written on the right.)
]
#sol[
  Let $U subset S$ be an open set. Then
  $
    pi^(-1)(pi(U)) &= union.big_(g in G) U g
  $
  is open in $S$ as a union of open sets. Since $pi$ is a quotient map, $pi(U)$ is open in $S \/ G$. Therefore, $pi$ is an open map.
]

#prob[
  Let the additive group $2pi ZZ$ act on $RR$ on the right by $x dot 2pi n = x + 2pi n$, where $n$ is an integer. Show that the orbit space $RR \/ 2pi ZZ$ is a smooth manifold.
]
#sol[
  + $RR \/ 2pi ZZ$ is Hausdorff. \
    Let $[x], [y] in RR \/ 2pi ZZ$ be two distinct points and presentatives $x in [x], y in [y]$. As $RR$ is Hausdorff, there are open sets $U, V subset RR$ such that $x in U$, $y in V$, and $U inter V = nothing$. Then $pi(U) $ and $pi(V)$ are open sets in $RR \/ 2pi ZZ$ as $pi$ is an open map, moreover, $pi(U) inter pi(V) = nothing$. Therefore, $RR \/ 2pi ZZ$ is Hausdorff.
  + $RR \/ 2pi ZZ$ is second countable. \
    As $pi$ is an open map and $RR$ is second countable, $RR \/ 2pi ZZ$ is second countable.
  + $RR \/ 2pi ZZ$ is locally Euclidean. \
    Define
    $
      phi_1: RR \/ 2pi ZZ &-> (-pi, pi) \
      [x] &mapsto x in (-pi, pi),
    $
    and
    $
      phi_2: RR \/ 2pi ZZ &-> (0, 2pi) \
      [x] &mapsto x in (0, 2pi).
    $
    On $phi_1(U_1 inter U_2) = phi_1(RR \/ 2pi ZZ) = (-pi, pi)$, 
    + $x in (-pi, 0)$
      $
        phi_2 compose phi_1^(-1)(x) &= phi_2([x]) \
        &= x + 2pi.
      $
    + $x in (0, pi)$
      $
        phi_2 compose phi_1^(-1)(x) &= phi_2([x]) \
        &= x.
      $
    On $phi_2(U_1 inter U_2) = phi_2(RR \/ 2pi ZZ) = (0, 2pi)$,
    + $x in (0, pi)$
      $
        phi_1 compose phi_2^(-1)(x) &= phi_1([x]) \
        &= x.
      $
    + $x in (pi, 2pi)$
      $
        phi_1 compose phi_2^(-1)(x) &= phi_1([x]) \
        &= x - 2pi.
      $
    Therefore, $(RR \/ 2pi ZZ, phi_1)$ and $(RR \/ 2pi ZZ, phi_2)$ are compatible and then form a $C^infinity$ atlas. Then, $RR \/ 2pi ZZ$ is locally Euclidean.
  In conclusion, $RR \/ 2pi ZZ$ is a smooth manifold.
]

#prob[
  + Let ${(U_alpha, phi.alt_alpha)}_(alpha=1)^2$ be the atlas of the circle $S^1$ in Example 5.7, and let $macron(phi.alt)_alpha$ be the map $phi.alt_alpha$ followed by the projection $RR -> RR \/ 2pi ZZ$. On $U_1 inter U_2 = A union.sq B$, since $phi.alt_1$ and $phi.alt_2$ differ by an integer multiple of $2pi$, $macron(phi.alt)_1 = macron(phi.alt)_2$. Therefore, $macron(phi.alt)_1$ and $macron(phi.alt)_2$ piece together to give a well-defined map $macron(phi.alt): S^1 -> RR \/ 2pi ZZ$. Prove that $macron(phi.alt)$ is $C^infinity$.
  
  + The complex exponential $RR -> S^1$, $t |-> e^(i t)$, is constant on each orbit of the action of $2pi ZZ$ on $RR$. Therefore, there is an induced map $F: RR \/ 2pi ZZ -> S^1$, $F([t]) = e^(i t)$. Prove that $F$ is $C^infinity$.
  
  + Prove that $F: RR \/ 2pi ZZ -> S^1$ is a diffeomorphism.
]
#sol[
  + $
      U_1 &= {e^(i t) in CC | - pi lt t lt pi}, \
      U_2 &= {e^(i t) in CC | 0 lt t lt 2 pi},
    $
    and
    $
      phi.alt_1(e^(i t)) &= t, quad -pi lt t lt pi, \
      phi.alt_2(e^(i t)) &= t, quad 0 lt t lt 2 pi,
    $
    Let $pi: RR -> RR \/ 2pi ZZ$ be the projection map and $psi_1: RR \/ 2pi ZZ -> V_1 = (-pi, pi)$ and $psi_2: RR \/ 2pi ZZ -> V_2 = (0, 2pi)$ be the coordinate maps. 
    #figure(
      diagram({
      let (a, b, c, d) = ((-1, -1), (1, -1), (-1, 1), (1, 1))
      node(a, $S^1$)
      node(b, $RR \/ 2 pi ZZ$)
      node(c, $phi.alt_alpha (U_alpha)$)
      node(d, $V_beta$)
      edge(a, b, $macron(phi.alt)$, "->")
      edge(a, c, $phi.alt_alpha$, "->")
      edge(c, b, $pi$, "->")
      edge(b, d, $psi_beta$, "->")
    }))
    + $
        psi_1 compose macron(phi.alt) compose phi.alt_1^(-1)(x) &= psi_1 compose pi (x) \
        &= x, quad -pi lt x lt pi.
      $
    + $
        psi_2 compose macron(phi.alt) compose phi.alt_1^(-1)(x) &= psi_2 compose pi (x) \
        &= cases(
          x quad 0 lt x lt pi \
          x + 2pi quad -pi lt x lt 0
        )
      $
    + $
        psi_1 compose macron(phi.alt) compose phi.alt_2^(-1)(x) &= psi_1 compose pi (x) \
        &= cases(
          x quad 0 lt x lt pi \
          x - 2pi quad pi lt x lt 2pi
        )
      $
    + $
        psi_2 compose macron(phi.alt) compose phi.alt_2^(-1)(x) &= psi_2 compose pi (x) \
        &= x, quad 0 lt x lt 2pi.
      $
    Then, $psi_beta compose macron(phi.alt) compose phi.alt_alpha^(-1)$ is $C^infinity$. Since $psi_beta$ and $psi_alpha$ are diffeomorphisms, $macron(phi.alt)$ is $C^infinity$.
  + #figure(
      diagram({
      let (a, b, c, d) = ((-1, -1), (1, -1), (-1, 1), (1, 1))
      node(a, $S^1$)
      node(b, $RR \/ 2 pi ZZ$)
      node(c, $phi.alt_alpha (U_alpha)$)
      node(d, $V_beta$)
      edge(b, a, $F$, "->")
      edge(a, c, $phi.alt_alpha$, "->")
      edge(b, d, $psi_beta$, "->")
    }))
    + $
        phi.alt_1 compose F compose psi_1^(-1)(x) &= phi.alt_1 compose F ([x]) \
        &= phi.alt_1 (e^(i x)) \
        &= x, quad -pi lt x lt pi.
      $
    + $
        phi.alt_2 compose F compose psi_1^(-1)(x) &= phi.alt_2 compose F ([x]) \
        &= phi.alt_2 (e^(i x)) \
        &= cases(
          x quad 0 lt x lt pi \
          x + 2pi quad -pi lt x lt 0
        )
      $
    + $
        phi.alt_1 compose F compose psi_2^(-1)(x) &= phi.alt_1 compose F ([x]) \
        &= phi.alt_1 (e^(i x)) \
        &= cases(
          x quad 0 lt x lt pi \
          x - 2pi quad pi lt x lt 2pi
        )
      $
    + $
        phi.alt_2 compose F compose psi_2^(-1)(x) &= phi.alt_2 compose F ([x]) \
        &= phi.alt_2 (e^(i x)) \
        &= x, quad 0 lt x lt 2pi.
      $
    Then, $phi.alt_beta compose F compose psi_alpha^(-1)$ is $C^infinity$. Since $psi_beta$ and $psi_alpha$ are diffeomorphisms, $F$ is $C^infinity$.
  + 
]

#prob[
  The Grassmannian $G(k,n)$ is the set of all $k$-planes through the origin in $RR^n$. Such a $k$-plane is a linear subspace of dimension $k$ of $RR^n$ and has a basis consisting of $k$ linearly independent vectors $a_1,...,a_k$ in $RR^n$. It is therefore completely specified by an $n times k$ matrix $A = [a_1 ... a_k]$ of rank $k$, where the rank of a matrix $A$, denoted by $"rk"A$, is defined to be the number of linearly independent columns of $A$. This matrix is called a matrix representative of the $k$-plane.
  
  Two bases $a_1,...,a_k$ and $b_1,...,b_k$ determine the same $k$-plane if there is a change-of-basis matrix $g = [g_(i j)] in "GL"(k, RR)$ such that
  
  $
    b_j = sum_i a_i g_(i j), quad 1 <= i,j <= k.
  $
  
  In matrix notation, $B = A g$.
  
  Let $F(k,n)$ be the set of all $n times k$ matrices of rank $k$, topologized as a subspace of $RR^(n times k)$, and $tilde$ the equivalence relation
  
  $
    A tilde B quad "iff" quad text("there is a matrix") g in "GL"(k, RR) text(" such that") B = A g.
  $
  
  In the notation of Problem B.3, $F(k,n)$ is the set $D_"max"$ in $RR^(n times k)$ and is therefore an open subset. There is a bijection between $G(k,n)$ and the quotient space $F(k,n)/tilde$. We give the Grassmannian $G(k,n)$ the quotient topology on $F(k,n)/tilde$.
  
  + Show that $tilde$ is an open equivalence relation. (Hint: Either mimic the proof of Proposition 7.14 or apply Problem 7.5.)
  
  + Prove that the Grassmannian $G(k,n)$ is second countable. (Hint: Apply Corollary 7.10.)
  
  + Let $S = F(k,n)$. Prove that the graph $R$ in $S times S$ of the equivalence relation $tilde$ is closed. (Hint: Two matrices $A = [a_1 ... a_k]$ and $B = [b_1 ... b_k]$ in $F(k,n)$ are equivalent if and only if every column of $B$ is a linear combination of the columns of $A$ if and only if $"rk"[A B] <= k$ if and only if all $(k + 1) times (k + 1)$ minors of $[A B]$ are zero.)
  
  + Prove that the Grassmannian $G(k,n)$ is Hausdorff. (Hint: Mimic the proof of Proposition 7.16.)
  
  Next we want to find a $C^infinity$ atlas on the Grassmannian $G(k,n)$. For simplicity, we specialize to $G(2,4)$. For any $4 times 2$ matrix $A$, let $A_(i j)$ be the $2 times 2$ submatrix consisting of its $i$th row and $j$th row. Define
  
  $
    V_(i j) = {A in F(2,4) | A_(i j) text(" is nonsingular")}.
  $
  
  Because the complement of $V_(i j)$ in $F(2,4)$ is defined by the vanishing of $det A_(i j)$, we conclude that $V_(i j)$ is an open subset of $F(2,4)$.
  #set enum(start: 5)
  + Prove that if $A in V_(i j)$, then $A g in V_(i j)$ for any nonsingular matrix $g in "GL"(2, RR)$.
  
  + Define $U_(i j) = V_(i j) / tilde$. Since $tilde$ is an open equivalence relation, $U_(i j) = V_(i j) / tilde$ is an open subset of $G(2,4)$.
  
  For $A in V_(12)$,
  
  $
    A tilde A A_(12)^(-1) = mat(
      1, 0;
      0, 1;
      *, *;
      *, *
    ) = mat(
      I;
      A_(34)A_(12)^(-1)
    ).
  $
  
  This shows that the matrix representatives of a 2-plane in $U_(12)$ have a canonical form $B$ in which $B_(12)$ is the identity matrix.
  
  + Show that the map $tilde(phi)_(12): V_(12) -> RR^(2 times 2)$,
  
  $
    tilde(phi)_(12)(A) = A_(34)A_(12)^(-1),
  $
  
  induces a homeomorphism $phi_(12): U_(12) -> RR^(2 times 2)$.
  
  + Define similarly homeomorphisms $phi_(i j): U_(i j) -> RR^(2 times 2)$. Compute $phi_(12) compose phi_(23)^(-1)$, and show that it is $C^infinity$.
  
  + Show that ${U_(i j) | 1 <= i < j <= 4}$ is an open cover of $G(2,4)$ and that $G(2,4)$ is a smooth manifold.
  
  Similar consideration shows that $F(k,n)$ has an open cover ${V_I}$, where $I$ is a strictly ascending multi-index $1 <= i_1 < ... < i_k <= n$. For $A in F(k,n)$, let $A_I$ be the $k times k$ submatrix of $A$ consisting of $i_1$th, ..., $i_k$th rows of $A$. Define
  
  $
    V_I = {A in G(k,n) | det A_I != 0}.
  $
  
  Next define $tilde(phi)_I: V_I -> RR^((n-k) times k)$ by
  
  $
    tilde(phi)_I(A) = (A A_I^(-1))_(I'),
  $
  
  where $()_(I')$ denotes the $(n - k) times k$ submatrix obtained from the complement $I'$ of the multi-index $I$. Let $U_I = V_I / tilde$. Then $tilde(phi)$ induces a homeomorphism $phi: U_I -> RR^((n-k) times k)$. It is not difficult to show that ${(U_I, phi_I)}$ is a $C^infinity$ atlas for $G(k,n)$. Therefore the Grassmannian $G(k,n)$ is a $C^infinity$ manifold of dimension $k(n - k)$.
]

#prob[
  Show that the real projective space $RR P^n$ is compact.
]