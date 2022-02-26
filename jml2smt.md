## JML Generalized Quantifiers Translation to SMT

In the following,

-   `x` is a Java variable name
-   `T` is a Java numeric type
-   `E`, `E1`, and `E2` are expressions
-   [[`E`]] is the translation function of `E` assuming `E` is type checked.
-   Range is an expression that may refer to `x`
-   Body is an expression that may refer to `x`

Every instance of a JML generalized quantifiers have two SMT translation parts: a declaration and a usage.

### sum

Declaration:

```smt
[[|(\sum T x; Range; Body)|]] =>
   (define-fun-rec sum_N
      ((lo T) (x T)) Int
      (ite (< x lo)
         0
         (+
            (sum_N lo (- x 1))
            (ite [[Range]]
                [[Body]]
                0
            )
         )
      )
   )
```

where `sum_N` is a fresh identifier.

Usage:

```smt
(sum_N lo hi)        iff Range => lo < x && x < hi
(sum_N T.min, T.max) iff T has a minimum and maximum value
(0)                  otherwise, warn user
```

### num_of

num_of is translated to a sum expression

```smt
[[|(\num_of T x; Range; Body)|]]
   =>
      [[|(\sum T x; Range && Body; 1)|]]
```

### product

Declaration:

```smt
[[|(\product T x; Range; Body)|]] =>
   (define-fun-rec product_N
      ((lo T) (x T)) Int
      (ite (< x lo)
         1
         (*
            (product_N lo (- x 1))
            (ite [[Range]]
                [[Body]]
                1
            )
         )
      )
   )
```

where `product_N` is a fresh identifier.

Usage:

```smt
(product_N lo hi)        iff Range => lo < x && x < hi
(product_N T.min, T.max) iff T has a minimum and maximum value
(1)                      otherwise, warn user
```

## general expressions

```smt
[[(E)]]         => [[E]]
[[E1 || E2]]    => (or [[E1]] [[E2]])
[[E1 && E2]]    => (and [[E1]] [[E2]])
[[E1 == E2]]    => (= [[E1]] [[E2]])
[[E1 != E2]]    => (not (= [[E1]] [[E2]]))
[[E1 op E2]]    => (op [[E1]] [[E2]])    where op in {<, >, <=, >=, +, -, *}
[[E1 / E2]]     => (div [[E1]] [[E2]])   iff E1 and E2 are ints
[[E1 / E2]]     => (/ [[E1]] [[E2]])     iff E1 and E2 are reals
[[E1 % E2]]     => (mod [[E1]] [[E2]])   iff E1 and E2 are ints
[[E1 % E2]]     => (% [[E1]] [[E2]])     iff E1 and E2 are reals
[[! E]]         => (not E)
[[E ? E1 : E2]] => (ite [[E]] [[E1]] [[E2]])
```

## examples

`python python/parser.py -s`

```smt
; Input: (\sum int x; 0 <= x && x < 5; x) == 1 + 2 + 3 + 4;

; DECLARATION TRANSLATION OF SUM
    (define-fun-rec sum1
        ((lo Int) (x Int)) Int
        (ite (< x lo)
            0
            (+
                (sum1 lo (- x 1))
                (ite [[0 <= x && x < 5]]
                    [[x]]
                    0
                )
            )
        )
    )

    (define-fun-rec sum1
        ((lo Int) (x Int)) Int
        (ite (< x lo)
            0
            (+
                (sum1 lo (- x 1))
                (ite (and [[0 <= x]] [[x < 5]])
                    [[x]]
                    0
                )
            )
        )
    )

    (define-fun-rec sum1
        ((lo Int) (x Int)) Int
        (ite (< x lo)
            0
            (+
                (sum1 lo (- x 1))
                (ite (and (<= [[0]] [[x]]) (< [[x]] [[5]]))
                    [[x]]
                    0
                )
            )
        )
    )

    (define-fun-rec sum1
        ((lo Int) (x Int)) Int
        (ite (< x lo)
            0
            (+
                (sum1 lo (- x 1))
                (ite (and (<= 0 x) (< x 5))
                    [[x]]
                    0
                )
            )
        )
    )

    (define-fun-rec sum1
        ((lo Int) (x Int)) Int
        (ite (< x lo)
            0
            (+
                (sum1 lo (- x 1))
                (ite (and (<= 0 x) (< x 5))
                    x
                    0
                )
            )
        )
    )


; USAGE TRANSLATIONS
[[|(\sum x; 0 <= x && x < 5; x)| == 1 + 2 + 3 + 4]]
(= [[|(\sum x; 0 <= x && x < 5; x)|]] [[1 + 2 + 3 + 4]])
(= (sum1 0 5) (+ [[1 + 2 + 3]] [[4]]))
(= (sum0 0 5) (+ (+ [[1 + 2]] [[3]]) 4))
(= (sum0 0 5) (+ (+ (+ [[1]] [[2]]) 3) 4))
(= (sum0 0 5) (+ (+ (+ 1 2) 3) 4))
```
