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
    f: ]-pi/2, pi/2[n -> RR^n, f(x_1, ..., x_n) = (tan x_1, ..., tan x_n), 
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

