#import "../Assignment.typ": *
#show heading.where(level: 1): set heading(numbering: "1")
#set enum(start: 0)
#set enum(numbering: "(a)")
#show enum: it => {
  if it.start != 0 { return it }
  let args = it.fields()
  let items = args.remove("children")
  context enum(..args, start: item-counter.get().first() + 1, ..items)
  item-counter.update(i => i + it.children.len())
}
#section[Smooth Functions on a Euclidean Space]

#prob[
  Let $g(x) = 3/4 x^(3/4)$. Show that the function $h(x) = integral_0^x g(t) dif t$ is $C^2$ but not $C^3$ at $x = 0$.
]

#sol[
  $ h(x) &= integral_0^x g(t) dif t \
  &= 9/28 x^(7/3), $
  which is countinious at $x = 0$, thus $h$ is $C^0$ at $x = 0$. \
  $h'(x) = g(x) = 3/4 x^(3/4)$ is countinious at $x = 0$, thus $h$ is $C^1$ at $x = 0$. \
  $ h''(x) = g'(x) = x^(1/3), $
  which is countinious at $x = 0$, thus $h$ is $C^2$ at $x = 0$. \
  $ h'''(x) = g''(x) = 1/3 x^(-2/3), $
  which is not countinious at $x = 0$, thus $h$ is not $C^3$ at $x = 0$. \
]

#prob[
  Let $ f(x) = cases(
    e^(-1/x) quad & x > 0,
    0 & x lt.eq 0.
  ) $
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
  $ f^((k+1))(x) &= dif/(dif x) f^((k))(x) \
  &= dif/(dif x) (p_(2n)(1/x)e^(-1/x)) \
  &= dif/(dif x) (p_(2n)(1/x)) e^(-1/x) + p_(2n)(1/x) dif/(dif x) e^(-1/x) \
  &= dif/(dif x) [a_(2k) (1/x)^(2k)+ dots.c] e^(-1/x) + [a_(2k) (1/x)^(2k)+ dots.c] 1/x^2 e^(-1/x) \
  &= [-2k a_(2k) (1/x)^(2k+1) + a_(2k) (1/x)^(2k+2) + dots.c] e^(-1/x) \
  &= p_(2(k+1))(1/x)e^(-1/x), $
  where $p_(2(k+1))(y)$ is a polynomial of degree $2(k+1)$ in $y$. This completes the inductive step.
  + From the result of part (a), we know that for any $k gt.eq 0$, 
  $ f^((k))(x) = p_(2k)(1/x)e^(-1/x), $ where $p_(2k)(y)$ 
  is a polynomial of degree $2k$. Then we can evaluate the limit as $x$ approaches $0$ from the right:
  $ lim_(x arrow.r 0^+) f((k)) (x) &= lim_(x arrow.r 0^+) p_(2k)(1/x)e^(-1/x) \
  &= 0, $
  which implies that $f^((k))(0) = 0$ for all $k gt.eq 0$, and thus $f$ is $C^infinity$ on $RR$.
]

#prob[
  Let $U, V in RR^n$ be two open sets. A $C^infinity$ map $F: U arrow.r V$ is called a diffeomorphism if it is bijective and has a $C^infinity$ inverse $F^(-1): V arrow.r U$.
  + Show that the function $f:(-pi/2, pi/2) arrow.r RR$, $f(x) = tan x$, is a diffeomorphism.
  + Let $a, b$ be real numbers with $a < b$. Find a linear function $h:(a, b) arrow.r (-1, 1)$, thus proving that any finite open intervals are diffeomorphic.
  + The composite $f circle.small h: (a, b) arrow.r RR$ is then a diffeomorphism of an open interval with $RR$.
  + The exponential function exp: $RR arrow.r (0, infinity)$ is a diffeomorphism. Use it to show that for any real numbers $a$ and $b$, the intervals $RR, (a, infinity)$, and $(-infinity, b)$ are diffeomorphic.
]