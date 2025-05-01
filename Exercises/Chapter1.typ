#import "../Assignment.typ": *
#show: noteworthy.with(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: "An Introduction to Manifold",
  author: "Vivi",
  contact-details: "Chapter 1",
)
#section[Smooth Functions on a Euclidean Space]

#prob[
  Let $g(x) = 3/4 x^(3/4)$. Show that the function $h(x) = integral_0^x g(t) dif t$ is $C^2$ but not $C^3$ at $x = 0$.
]

#sol[
  $ 
    h(x) &= integral_0^x g(t) dif t \
    &= 9/28 x^(7/3), 
  $
  which is countinious at $x = 0$, thus $h$ is $C^0$ at $x = 0$. \
  $h'(x) = g(x) = 3/4 x^(3/4)$ is countinious at $x = 0$, thus $h$ is $C^1$ at $x = 0$. \
  $ 
    h''(x) = g'(x) = x^(1/3), 
  $
  which is countinious at $x = 0$, thus $h$ is $C^2$ at $x = 0$. \
  $ 
    h'''(x) = g''(x) = 1/3 x^(-2/3), 
  $
  which is not countinious at $x = 0$, thus $h$ is not $C^3$ at $x = 0$. \
]

#prob[
Let $ 
  f(x) = cases(
    e^(-1/x) quad & x > 0,
    0 & x lt.eq 0.
  ) 
$
+ Show by induction that for $x > 0$ and $k > 0$, the $k$-th derivative $f^((k)) (x)$ is of the form $p_(2k) e^(-1/x)$ for some polynomial $p_(2k)(y)$ of degree $2k$ in $y$.
+ Prove that $f$ is $C^infinity$ on $RR$ an that $f^((k)) (0) = 0$ for all $k gt.eq 0$.
]

#sol[
+ Let $k = 0$, for $x > 0$, we have
  $ f^((x)) &= f(x)\
  &= e^(-1/x)\
  &= p_0(1/x)e^(-1/x), $
  where $p_0(y) = 1$. This is a polynomial of degree $0$ in $y$. Thus the base case holds.
  Then assume the inductive hypothesis holds for $k = n$, i.e., $f^((n))(x) = p_(2n)(1/x)e^(-1/x)$, where $p_(2n)(y)$ is a polynomial of degree $2n$. We will show it holds for $k = n + 1$:
  $ 
    f^((k+1))(x) &= dif/(dif x) f^((k))(x) \
    &= dif/(dif x) (p_(2n)(1/x)e^(-1/x)) \
    &= dif/(dif x) (p_(2n)(1/x)) e^(-1/x) + p_(2n)(1/x) dif/(dif x) e^(-1/x) \
    &= dif/(dif x) [a_(2k) (1/x)^(2k)+ dots.c] e^(-1/x) + [a_(2k) (1/x)^(2k)+ dots.c] 1/x^2 e^(-1/x) \
    &= [-2k a_(2k) (1/x)^(2k+1) + a_(2k) (1/x)^(2k+2) + dots.c] e^(-1/x) \
    &= p_(2(k+1))(1/x)e^(-1/x), 
  $
  where $p_(2(k+1))(y)$ is a polynomial of degree $2(k+1)$ in $y$. This completes the inductive step.
+ From the result of part (a), we know that for any $k gt.eq 0$, 
  $ 
    f^((k))(x) = p_(2k)(1/x)e^(-1/x), 
  $ where $p_(2k)(y)$ 
  is a polynomial of degree $2k$. Then we can evaluate the limit as $x$ approaches $0$ from the right:
  $ 
    lim_(x arrow.r 0^+) f((k)) (x) &= lim_(x arrow.r 0^+) p_(2k)(1/x)e^(-1/x) \
    &= 0, 
  $
  which implies that $f^((k))(0) = 0$ for all $k gt.eq 0$, and thus $f$ is $C^infinity$ on $RR$.
]

#prob[
  Let $U subset RR^n$ and $V subset RR^n$ be open subsets. A $C^infinity$ map $F: U -> V$ is called a _diffeomorphism_ if it is bijective and has a $C^infinity$ inverse $F^(-1): V -> U$.
  + Show that the function $f: ]-pi/2, pi/2[ -> RR$, $f(x) = tan x$, is a diffeomorphism.
  + Let $a, b$ be real numbers with $a < b$. Find a linear function $h: ]a, b[ -> ]-1, 1[$, thus proving that any two finite open intervals are diffeomorphic.
  + The composite $f compose h: ]a, b[ -> RR$ is then a diffeomorphism of an open interval with $RR$.
  + The exponential function $exp: RR -> ]0, infinity[$ is a diffeomorphism. Use it to show that for any real numbers $a$ and $b$, the intervals $RR$, $]a, infinity[$, and $]-infinity, b[$ are diffeomorphic.
]

#prob[
  Show that the map
  $ 
    f: ]-pi/2, pi/2[n -> RR^n, f(x_1, dots.c, x_n) = (tan x_1, dots.c, tan x_n), 
  $
  is a diffeomorphism.
]

#prob[
  Let $B(0, 1)$ be the open unit disk in $RR^2$. To find a diffeomorphism between $B(0, 1)$ and $RR^2$, we identify $RR^2$ with the $x y$-plane in $RR^3$ and introduce the lower open hemisphere
  $ S: x^2 + y^2 + (z - 1)^2 = 1, quad z < 1, $
  in $RR^3$ as an intermediate space.
  + The stereographic projection $g: S -> RR^2$ from $(0, 0, 1)$ is the map that sends a point $(a, b, c) in S$ to the intersection of the line through $(0, 0, 1)$ and $(a, b, c)$ with the $x y$-plane. Show that it is given by
    $ 
      (a, b, c) arrow.r.bar (u, v) = (a/(1-c), b/(1-c)), quad c = 1 - sqrt(1 - a^2 - b^2), 
    $
    with inverse
    $ 
      (u, v) arrow.r.bar (u/sqrt(1 + u^2 + v^2), v/sqrt(1 + u^2 + v^2), 1 - 1/sqrt(1 + u^2 + v^2)). 
    $
  + Composing the maps $f$ and $g$ gives the map
    $ 
      h = g compose f: B(0, 1) -> RR^2, quad h(a, b) = (a/sqrt(1 - a^2 - b^2), b/sqrt(1 - a^2 - b^2)). 
    $
    Find a formula for $h^(-1)(u, v) = (f^(-1) compose g^(-1))(u, v)$ and conclude that $h$ is a diffeomorphism of the open disk $B(0, 1)$ with $RR^2$.
  + Generalize part (b) to $RR^n$.
]

#prob[
  Prove that if $f: RR^2 -> RR$ is $C^infinity$, then there exist $C^infinity$ functions $g_(11), g_(12), g_(22)$ on $RR^2$ such that
  $ 
    f(x, y) = f(0, 0) + (diff f)/(diff x)(0, 0)x + (diff f)/(diff y)(0, 0)y + x^2 g_(11)(x, y) + x y g_(12)(x, y) + y^2 g_(22)(x, y). 
  $
]

#sol[
  Applying Taylor's theorem with remainder, we have
  $ 
    f(x, y) = f(0, 0) + x f_1(x, y) + y f_2(x, y), 
  $
  where $f_1(x, y) = (diff f)/(diff x)(x, y)$ and $f_2(x, y) = (diff f)/(diff y)(x, y)$。

  As $f$ is $C^infinity$, $f_1(x, y)$ and $f_2(x, y)$ are also $C^infinity$. we can expand $f_1(x, y)$ and $f_2(x, y)$ using Taylor's theorem with remainder around $(0, 0)$:
  $ 
    f_1(x, y) &= f_1(0, 0) + x f_(11)(x, y) + y f_(12)(x, y), \
    f_2(x, y) &= f_2(0, 0) + x f_(21)(x, y) + y f_(22)(x, y). 
  $

  Then, we can substitute these expansions back into the expression for $f(x, y)$:
  $ 
    f(x, y) &= f(0, 0) + x (f_1(0, 0) + x f_(11)(x, y) + y f_(12)(x, y)) + y (f_2(0, 0) + x f_(21)(x, y) + y f_(22)(x, y)) \
    &= f(0, 0) + (diff f)/(diff x)(0, 0)x + (diff f)/(diff y)(0, 0)y + x^2 f_(11)(x, y) + 2x y f_(12)(x, y) + y^2 f_(22)(x, y). 
  $

  Then by defining $g_(11)(x, y) = f_(11)(x, y)$, $g_(12)(x, y) = 2f_(12)(x, y)$, and $g_(22)(x, y) = f_(22)(x, y)$, we get the desired result.
]

#prob[
  Let $f: RR^2 -> RR$ be a $C^infinity$ function with $f(0, 0) = (diff f)/(diff x)(0, 0) = (diff f)/(diff y)(0, 0) = 0$. Define
  $ 
    g(t, u) = cases(
      f(t, t u)/t & "for" t != 0,
      0 & "for" t = 0.
    ) 
  $
  Prove that $g(t, u)$ is $C^infinity$ for $(t, u) in RR^2$. (Hint: Apply Problem 1.6.)
]

#prob[
  Define $f: RR -> RR$ by $f(x) = x^3$. Show that $f$ is a bijective $C^infinity$ map, but that $f^(-1)$ is not $C^infinity$. (This example shows that a bijective $C^infinity$ map need not have a $C^infinity$ inverse. In complex analysis, the situation is quite different: a bijective holomorphic map $f: CC -> CC$ necessarily has a holomorphic inverse.)
]

#section[Tangent Vectors in $RR^n$ as Derivations]

#prob[
  Let $X$ be the vector field $x diff / (diff x) + y diff / (diff y)$ and $f(x, y, z)$ the function $x^2 + y^2 + z^2$ on $RR^3$. Compute $X f$.
]

#sol[
  $ 
    X f &= (x diff/(diff x) + y diff/(diff y)) (x^2 + y^2 + z^2) \
    &= 2x^2 + 2y^2 
  $
]

#prob[
  Define carefully addition, multiplication, and scalar multiplication in $C_p^infinity$. Prove that addition in $C_p^infinity$ is commutative.
]

#sol[
  Let $[f]_p, [g]_p in C_p^infinity$. We define the addition of two equivalence classes as follows:
  $ 
    [f]_p + [g]_p = [f + g]_p, 
  $
  where $f + g$ is the pointwise sum of the functions $f$ and $g$. \
  The multiplication of two equivalence classes is defined as:
  $ 
    [f]_p dot [g]_p = [f g]_p, 
  $
  where $f g$ is the pointwise product of the functions $f$ and $g$. \
  The scalar multiplication of an equivalence class by a scalar $c in RR$ is defined as:
  $ 
    c[f]_p = [c f]_p, 
  $
  where $c f$ is the pointwise product of the function $f$ and the scalar $c$.
]

#prob[
  Let $D$ and $D'$ be derivations at $p$ in $RR^n$, and $c in RR$. Prove that
  + the sum $D + D'$ is a derivation at $p$.
  + the scalar multiple $c D$ is a derivation at $p$.
]

#sol[
  + Let $f, g in C^infinity(RR^n)$, then we have
    $ 
      (D + D')(f g) &= D(f g) + D'(f g) \
      &= D(f)g(p) + f(p)D(g) + D'(f)g(p) + f(p)D'(g) \
      &= (D(f) + D'(f))g(p) + f(p)(D(g) + D'(g)) \
      &= (D + D')(f)g(p) + f(p)(D + D')(g). 
    $
  + $ 
      (c D)(f g) &= c D(f g) \
      &= c(D(f)g(p) + f(p)D(g)) \
      &= c D(f)g(p) + c f(p)D(g) \
      &= (c D)(f)g(p) + f(p)(c D)(g). 
    $
]

#prob[
  Let $A$ be an algebra over a field $K$. If $D_1$ and $D_2$ are derivations of $A$, show that $D_1 compose D_2$ is not necessarily a derivation (it is if $D_1$ or $D_2 = 0$), but $D_1 compose D_2 - D_2 compose D_1$ is always a derivation of $A$.
]

#sol[
  Let $f: RR -> RR$ be a function such that $f(x) = x$, and let $D_1 = D_2 = dif/(dif x)$. Then, for the Lebniz rule, we have
  $ 
    D_1 compose D_2(f f) &= dif/(dif x) (dif/(dif x) (x^2)) \
    &= dif/(dif x) (2x) \
    &= 2, 
  $
  but
  $ 
    (D_2 compose D_1)(f)f(p) + f(p)(D_2 compose D_1)(f) &= dif^2 x/(dif x^2) p + p dif^2 x/(dif x^2) \
    &= 0. 
  $
  Therefore, $D_1 compose D_2$ is not a derivation. \
  Next, for $D_1 compose D_2 - D_2 compose D_1$, we examine the Lebniz rule:
  $ 
    (D_1 compose D_2 - D_2 compose D_1)(f g) &= D_1 compose D_2(f g) - D_2 compose D_1(f g) \
    &= D_1[D_2(f)g(p) + f(p)D_2(g)] \- D_2[D_1(f)g(p) + f(p)D_1(g)] \
    &= (D_1 compose D_2(f)g(p) + f(p)D_1 compose D_2(g)) \
    &- (D_2 compose D_1(f)g(p) + f(p)D_2 compose D_1(g)) \
    &= (D_1 compose D_2 - D_2 compose D_1)(f)g(p) + f(p)(D_1 compose D_2 - D_2 compose D_1)(g). 
  $
  Thus, $D_1 compose D_2 - D_2 compose D_1$ satisfies the Leibniz rule and is a derivation.
]

#section[The Exterior Algebra of Multivectors]

#prob[
  Let $e_1, dots.c, e_n$ be a basis for a vector space $V$ and let $alpha^1, dots.c, alpha^n$ be its dual basis in $V^V$. Suppose $[g_(i j)] in RR^(n times n)$ is an $n times n$ matrix. Define a bilinear function $f: V times V -> RR$ by
  $ 
    f(v, w) = g_(i j) v^i w^j 
  $
  for $v = v^i e_i$ and $w = w^j e_j$ in $V$. Describe $f$ in terms of the tensor products of $alpha^i$ and $alpha^j$, $1 <= i,j <= n$.
]
#sol[
  Since $v^i = alpha^i (v)$ and $w^j = alpha^j (w)$, we can express $f$ as follows:
  $
    f(v, w) &= g_(i j) v^i w^j \
    &= g_(i j) alpha^i (v) alpha^j (w) \
    &= g_(i j) (alpha^i times.circle alpha^j)(v, w),
  $
  then $f = g_(i j) (alpha^i times.circle alpha^j)$.
]

#prob[
  Let $V$ be a vector space of dimension $n$ and $f: V -> RR$ a nonzero linear functional.
  + Show that $dim ker f = n - 1$. A linear subspace of $V$ of dimension $n - 1$ is called a _hyperplane_ in $V$.
  + Show that a nonzero linear functional on a vector space $V$ is determined up to a multiplicative constant by its kernel, a hyperplane in $V$. In other words, if $f$ and $g: V -> RR$ are nonzero linear functionals and $ker f = ker g$, then $g = c f$ for some constant $c in RR$.
]
#sol[
  + $
      dim ker f &= dim V - dim im f \
      &= n - 1.
    $
  + Let $f, g: V arrow.r RR$ be nonzero linear functionals with $ker f = ker g$. As $f$ is nonzero, there exists $v'_0 in V$ such that $f(v'_0) = b eq.not 0$. Let $v_0 = v'_0 / b$, $f(v_0) = f(v'_0 / b) = 1 / b f(v'_0) = 1$. As $ker f = ker g$ and $f(v_0) eq.not 0$, we have $g(v_0) eq.not 0$. Then, let $v in V, f(v) = a$, and $w = v - a v_0$. As $f$ is linear,
  $
    f(w) &= f(v - a v_0) \
    &= f(v) - a f(v_0) \
    &= a - a \
    &= 0,
  $
  which means $w in ker f$, and thus $w in ker g$. Then,
  $
    0 &= g(w) \
    &= g(v - a v_0) \
    &= g(v) - a g(v_0) \
    &= g(v) - f(v) g(v_0).
  $
  Therefore we have that $g(v) = c f(v)$, where $c = g(v_0)$.
]

#prob[
  Let $V$ be a vector space of dimension $n$ with basis $e_1, dots.c, e_n$. Let $alpha^1, dots.c, alpha^n$ be the dual basis for $V^or$. Show that a basis for the space $L_k (V)$ of $k$-linear functions on $V$ is ${alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)}$ for all multi-indices $(i_1, dots.c, i_k)$ (not just the strictly ascending multi-indices as for $A_k (L)$). In particular, this shows that $dim L_k (V) = n^k$.
]

#sol[
  + Let $T in L_k (V)$ and $T(e_i_1, dots.c, e_i_k) = T_(i_1, dots.c, i_k)$, For the function
    $
      T' = T_(i_1, dots.c, i_k) alpha^(i_1) times.circle dots.c times.circle alpha^(i_k),
    $
    we have
    $
      T'(e_j_1, dots.c, e_j_k) &= T_(i_1, dots.c, i_k) alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)(e_j_1, dots.c, e_j_k) \
      &= T_(i_1, dots.c, i_k) alpha^(i_1)(e_j_1) dots.c alpha^(i_k)(e_j_k) \
      &= T_(i_1, dots.c, i_k) delta^(i_1)_(j_1) dots.c delta^(i_k)_(j_k) \
      &= T_(j_1, dots.c, j_k) \
      &= T(e_j_1, dots.c, e_j_k),
    $
    which means $T = T'$. Therefore, ${alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)}$ spans $L_k (V)$. \
  + Suppose $T = 0$, then
    $
      0 &= T(e_j_1, dots.c, e_j_k) \
      &= T_(i_1, dots.c, i_k) alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)(e_j_1, dots.c, e_j_k) \
      &= T_(i_1, dots.c, i_k) alpha^(i_1)(e_j_1) dots.c alpha^(i_k)(e_j_k) \
      &= T_(i_1, dots.c, i_k) delta^(i_1)_(j_1) dots.c delta^(i_k)_(j_k) \
      &= T_(j_1, dots.c, j_k),
    $
    which means $T_(i_1, dots.c, i_k) = 0$ for all $j_1, dots.c, j_k$. Therefore ${alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)}$ is linearly independent. \
  Thus, ${alpha^(i_1) times.circle dots.c times.circle alpha^(i_k)}$ is a basis for $L_k (V)$.
]

#prob[
  Let $f$ be a $k$-tensor on a vector space $V$. Prove that $f$ is alternating if and only if $f$ changes sign whenever two successive arguments are interchanged:
  $f(dots.c, v_(i+1), v_i, dots.c) = -f(dots.c, v_i, v_(i+1), dots.c)$
  for $i = 1, dots.c, k-1$.
]
#sol[
  + If $f$ is alternating, then for $sigma = (i, i+1)$,
    $
      f(dots.c, v_(i+1), v_i, dots.c) &= f(sigma(v_1), dots.c, sigma(v_k)) \
      &= "sgn"(sigma) f(v_1, dots.c, v_k) \
      &= -f(dots.c, v_i, v_(i+1), dots.c),
    $
    which means $f(dots.c, v_(i+1), v_i, dots.c) = -f(dots.c, v_i, v_(i+1), dots.c)$.
  + If $f(dots.c, v_(i+1), v_i, dots.c) = -f(dots.c, v_i, v_(i+1), dots.c)$, then for $sigma = (i, i+1)$,
    $
      f(sigma(v_1), dots.c, sigma(v_k)) &= f(dots.c, v_(i+1), v_i, dots.c) \
      &= -f(dots.c, v_i, v_(i+1), dots.c) \
      &= "sgn"(sigma) f(v_1, dots.c, v_k),
    $
    which means $f$ is alternating.
]

#prob[
  Let $f$ be a $k$-tensor on a vector space $V$. Prove that $f$ is alternating if and only if $f(v_1, dots.c, v_k) = 0$ whenever two of the vectors $v_1, dots.c, v_k$ are equal.
]
#sol[
  + If $f$ is alternating, and $v_i = v_j$, then for $sigma = (i, j)$,
    $
      f(dots.c, sigma(v_i), dots.c, sigma(v_j), dots.c) &= f(dots.c, v_j, dots.c, v_i, dots.c) \
      &= "sgn"(sigma) f(v_1, dots.c, v_k) \
      &= -f(dots.c, v_i, dots.c, v_j, dots.c),
    $
    which means $f(v_1, dots.c, v_k) = 0$.
  + If $f(v_1, dots.c, v_k) = 0$ for $v_i = v_j$, then for $sigma = (i, j)$,
    $
      0 &= f(dots.c, v_j, dots.c, v_i, dots.c) \
      &= - f(dots.c, v_i, dots.c, v_j, dots.c) \
      &= "sgn"(sigma) f(v_1, dots.c, v_k) \
      &= f(sigma(v_1), dots.c, sigma(v_k)) \
    $
    which means $f$ is alternating.
]

#prob[
  Let $V$ be a vector space. For $a, b in RR$, $f in A_k (V)$, and $g in A_l (V)$, show that $a f and b g = (a b) f and g$.
]
#sol[
  $
    a f and b g &= 1 / (k! l!) A(a f times.circle b g) \
    &= 1 / (k! l!) sum_(sigma in S_(k+l)) "sgn"(sigma) sigma(a f(v_1, dots.c, v_k) b g(v_(k+1), dots.c, v_(k+l))) \
    &= (a b) / (k! l!) sum_(sigma in S_(k+l)) "sgn"(sigma) sigma(f(v_1, dots.c, v_k) g(v_(k+1), dots.c, v_(k+l))) \
    &= (a b) / (k! l!) A(f times.circle g) \
    &= (a b) f and g,
  $
]

#prob[
  Suppose two sets of covectors on a vector space $V$, $beta^1, dots.c, beta^k$ and $gamma^1, dots.c, gamma^k$, are related by
  $ 
    beta^i = a_j^i gamma^j, quad i = 1, dots.c, k, 
  $
  for a $k times k$ matrix $A = [a_j^i]$. Show that
  $ 
    beta^1 and dots.c and beta^k = (det A) gamma^1 and dots.c and gamma^k. 
  $
]
#sol[
  $
    beta^1 and dots.c and beta^k &= (a^1_j_1 gamma^(j_1)) and dots.c and (a^k_j_k gamma^(j_k)) \
    &= a^1_j_1 dots.c a^k_j_k (gamma^(j_1) and dots.c and gamma^(j_k)) \
    &= a^1_sigma(1) dots.c a^k_sigma(k) ("sgn" sigma) (gamma^1 and dots.c and gamma^k) \
    &= (det A) (gamma^1 and dots.c and gamma^k).
  $
]

#prob[
  Let $f$ be a $k$-covector on a vector space $V$. Suppose two sets of vectors $u_1, dots.c, u_k$ and $v_1, dots.c, v_k$ in $V$ are related by
  $ 
    u_j = a_j^i v_i, quad j = 1, dots.c, k, 
  $
  for a $k times k$ matrix $A = [a_j^i]$. Show that
  $ 
    f(u_1, dots.c, u_k) = (det A) f(v_1, dots.c, v_k). 
  $
]
#sol[
  $
    f(u_1, dots.c, u_k) &= f(a_1^(i_1) v_i_1, dots.c, a_k^(i_k) v_i_k) \
    &= a_1^(i_1) dots.c a_k^(i_k) f(v_i_1, dots.c, v_i_k) \
    &= a_1^(sigma(1)) dots.c a_k^(sigma(k)) ("sgn" sigma) f(v_1, dots.c, v_k) \
    &= (det A) f(v_1, dots.c, v_k).
  $
]

#prob[
  Let $V$ be a vector space of dimension $n$. Prove that if an $n$-covector $omega$ vanishes on a basis $e_1, dots.c, e_n$ for $V$, then $omega$ is the zero covector on $V$.
]
#sol[
  Let ${e_1, dots.c, e_n}$ be a basis for $V$, for $v_i = v_i^j e_j$ in $V$, we have
  $
    omega(v_1, dots.c, v_n) &= det[v_i^j] omega(e_1, dots.c, e_n) \
    &= 0.
  $
]

#prob[
  Let $alpha^1, dots.c, alpha^k$ be 1-covectors on a vector space $V$. Show that $alpha^1 and dots.c and alpha^k != 0$ if and only if $alpha^1, dots.c, alpha^k$ are linearly independent in the dual space $V^V$.
]

#prob[
  Let $alpha$ be a nonzero 1-covector and $gamma$ a $k$-covector on a finite-dimensional vector space $V$. Show that $alpha and gamma = 0$ if and only if $gamma = alpha and beta$ for some $(k - 1)$-covector $beta$ on $V$.
]