# SMT

**Options:**

```smt
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :smt.mbqi true)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(set-option :verbose  10)
```

**Results:**

```smt
(check-sat) ; sat/unsat/unknown
(get-model) ; if sat get the example
(get-info :reason-unknown) ; unknown explaination
```

**Misc:**

Printing: `(echo "message")`
