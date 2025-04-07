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