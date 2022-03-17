## JML Generalized Quantifiers Translation to SMT

In the following,

-   `T` is a Java integral type (int, long, etc)
-   `K` is a Java numeric type
-   `x` is a Java variable name of type `T`
-   `E`, `E1`, and `E2` are expressions
-   [[`E`]] is the translation function of `E` assuming `E` is type checked
-   Range is an expression that may refer to `x` and returns type `boolean`
-   Body is an expression that may refer to `x` and returns type `K`

Every instance of a JML generalized quantifiers have two SMT translation parts: a declaration and a usage.

### sum

Declaration:

```smt
[[|(\sum T x; Range; Body)|]] =>
    (define-fun Range_N (x T) Bool [[Range]])
    (define-fun Body_N (x T) K [[Body]])

    (define-fun-rec sum_N
        ((lo T) (hi T)) K
        (ite (< hi lo)
            0
            (+
                (sum_N lo (- hi 1))
                (ite (Range_N hi)
                    (Body_N hi)
                    0
                )
            )
        )
    )
```

where `sum_N`, `range_N`, and `Body_N` are fresh identifiers.

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
    (define-fun Range_N (x T) Bool [[Range]])
    (define-fun Body_N (x T) K [[Body]])

    (define-fun-rec product_N
        ((lo T) (hi T)) K
        (ite (< hi lo)
            1
            (*
                (sum_N lo (- hi 1))
                (ite (Range_N hi)
                    (Body_N hi)
                    1
                )
            )
        )
    )
```

where `product_N`, `range_N`, and `Body_N` are fresh identifiers.

Usage:

```smt
(product_N lo hi)        iff Range => lo < x && x < hi
(product_N T.min, T.max) iff T has a minimum and maximum value
(1)                      otherwise, warn user
```

## multiple quantified variables

A JML quantifier expression with multiple variables, is syntactic sugar for nesting quantifiers.

```smt
[[|(Q T x1, x2, ..., xn; Range; Body)|]] =>
   [[(Q T x1; ; [[(Q T x2, ..., xn; Range; Body)]])]]

[[|(Q T x; ; Body)|]] => [[|(Q T x; true; Body)|]]
```

Where `Q` is a quantifier name (`\sum`, `\product`, `\num_of`, `\min`, or `\max`).

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

## bounds extracting

To initiate a quantifier call, the low and high bounds must be extracted from the range expression.

A minimal range must follow this pattern: `lo < i < hi`. The base implementation is from the [Runtime Assertion Checker](https://github.com/OpenJML/OpenJML/blob/master-module/OpenJDKModule/src/jdk.compiler/share/classes/org/jmlspecs/openjml/esc/JmlAssertionAdder.java#L17948). Our implementation can be found in the [JmlBoundsExtractor](https://github.com/OpenJML-SeniorDesign/OpenJML/blob/master-module/OpenJDKModule/src/jdk.compiler/share/classes/org/jmlspecs/openjml/esc/JmlBoundsExtractor.java#L64).

The following algorithm will be used:

```py
def extract(expression: Tree, isRoot: bool): ...

if isRoot and expression is not a binary AND or OR: warn('not supported')

# consider range: E1 && E2
if E1 is not binary: # E1 MUST be a boolean by the typechecker
    if E1 is True:   # the bounds are whatever the bounds of E2 are
    if E1 is False:  # the range is ALWAYS false, and lo = hi = 0 will suffice

if E2 is not binary: # E2 MUST be a boolean by the typechecker
    if E2 is True:   # the bounds are whatever the bounds of E1 are, if E1 was true, warn('not supported')
    if E2 is False:  # the range is ALWAYS false, and lo = hi = 0 will suffice

if expression is binary AND or OR:
    b1 = extract(lhs, False)
    b2 = extract(rhs, False)
    lo = (
        b1.lo              # if b1.lo not in decls and b2.lo in decls
        b2.lo              # if b1.lo in decls and b2.lo not in decls
        min(b1.lo, b2.lo)  # if b1.lo not in decls and b2.lo not in decls
        decls[0]           # otherwise
    )
    
    hi = (
        b1.hi              # if b1.hi not in decls and b2.hi in decls
        b2.hi              # if b1.hi in decls and b2.hi not in decls
        max(b1.hi, b2.hi)  # if b1.hi not in decls and b2.hi not in decls
        decls[0]           # otherwise
    )
    
    return Bounds(lo=lo, hi=hi)

if E is a binary comparison expression (<, <=, >, >=):
    # "orient" the comparison such that the lhs is small and rhs is large relative to each other
    return Bounds(lo=lhs, hi=rhs)

return Bounds(decls[0], decls[0]) or Bounds(lo=decls[0].type.MAX, hi=decls[0].type.MIN)
```

An expression being _in_ the decls list, means that the expression includes a quantified variable somewhere.

For instance let the decls be: `int i`, then, `i + 4` would be in decls, while `j + 4` is not. 

Additionally, if an expression is the parent of a binary leaf node and it is an OR expression, the user should recieve a warning. For example, `i < 0 || 4 < i`, should throw a warning because the range is functionally infinite. If there is no AND expression anywhere in the range, the range necessarily will be either 0 or infinite.

## example

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
