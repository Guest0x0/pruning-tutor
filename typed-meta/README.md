# Typed conversion and meta

## Introduction

This part is just a slight extension to the previous part (`untyped-meta`).
It features a *typed* conversion algorithm,
that is, two values are always checked for convertibility at some specified type.
Typed conversion can be used to implement `η` rules.
However, as in `untyped-meta` and `03-hole` of [[1]](#ref1),
η-conversion can be implemented *without* explicitly passing types, too.
However, more sophiscated type-directed conversion principles,
such as definitionally proof-irrelevant types,
cannot be handled without types.

There are two ways to implement typed conversion:

1. the "Tait's Yoga" style, where values are annotated with types.
(More specifically, the embedding `neutral -> value`,
as well as the arguments of a bound variable in a neutral term,
are annotated with types).

1. use untyped value representation and untyped normalization,
only pass the types around during conversion.

Here I will take the latter approach,
because the former will require *much*, *much more* bookkeeping during unification.

Another design choice is whether normalization should produce η-expanded terms.
The only place we need η is conversion.
However, conversion can be implemented on values directly.
So there's no need to produce η-long normal forms in normalization.

Actually, producing η-expanded terms in normalization has bad interaction with pattern unifcation.
Recall that in pattern unification,
the arguments of a meta variable must be a list of distinct bound variables.
However, if these variables are η-expanded,
the pattern condition will be violated syntactically,
and it is algorithmcally difficult (though possible) to invert the η-expansion.

Due to the above reasons, the final design of the type system in this part features:

1. untyped value representation
1. untyped normalization that does not perform any η-expansion
1. typed conversion

To implement typed conversion,
metas must be typed, otherwise there won't be enough type information.
So meta variables are typed in this part.


## Source code structure and reading guide

The source code structure is identical to `untyped-meta`:

- `Syntax.ml`: definition of core syntax, surface syntax and semantic values
- `MetaContext.ml`: context that maintains a global list of metas
- `Normalize.ml`: a simple untyped NBE algorithm
- `Unify.ml`: the main pattern unification algorithm with pruning
- `Typecheck.ml`: a simple bidirectional type checker
- `Pretty.ml`, `Parser.mly` and `Lexer.mll`: boring utilities
- `typedMetaTest.ml`: tests for the implementation. You can find some example programs here

Meta variables are now typed,
which requires some slight modification in `Syntax.ml`, `MetaContext.ml` and `Normalize.ml`.
However, the only interesting difference lies `Unify.ml`.


## Adapt for typed meta

For the unification algorithm,
the major effect of switching to typed meta happens at fresh meta allocation:
a type is now needed.
There are two sources of meta allocation in our unification algorithm:

1. Holes in surface syntax.
Assume we encounter a hole at context `Γ` with type `A`,
the corresponding meta should have type `Γ -> A`.
There's a pitfall here, though: *let-defined variables in* `Γ` *should not be added*.
See `env_to_tyfun` in `Unify.ml` for the implementation of this operation.

1. Flex-flex case in unification.
Assume we are applying a partial substitution `ρ` to a meta-headed term `?M x y`,
and the variable `x` should be pruned, then we need to allocate a fresh meta variable `?M'`,
and solve `?M` with `\$1. \$2. ?M' $2`.
What should be the type of `?M'`, then?
Assume the type of `?M` is `(x : X) -> (y : Y) -> Z`,
then `?M'` should have type `(y : Y) -> Z`.
But notice that we are working with a *dependently typed* theory, so `Y` may depend on `x`!
If `Y` indeed depend on `X`, then the equation will be ill-typed.
But even when `Y` does *not* depend on `X`, since we are using de Bruijin index/level,
`Y` lives in a context with `x` included, and we have to adjust its context.

## Handling type of meta in flex-flex

To properly handle the type of new metas in flex-flex case,
a new operation, `prune_tyfun` is implemented in `Unify.ml`.
It receives a pruning `pr` and a type `typ` (which is expected to be a function type),
prune away the arguments of `typ` according to `pr`,
and return the pruned, scope-safe type.

`prune_tyfun` reuses the partial substitution operation.
It maintains a partial substitution that forgets the pruned variables,
and applies it to the processed type all along the way.
See the `prune_tyfun` function in `Unify.ml` for more details.


## References

<a id="ref1" href="https://github.com/AndrasKovacs/elaboration-zoo">[1]</a>
<https://github.com/AndrasKovacs/elaboration-zoo>
