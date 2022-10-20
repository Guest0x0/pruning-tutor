# Typed conversion and meta

## Introduction

This part extends the previous part (`typed-meta`)
with a generalization of η-contraction.
It allow the arguments of meta variables to be not only bound variables,
but also "invertible" values, such as `\x. \y. f y x` where `f` is a bound variable.
The idea comes from [[1]](#ref1)[[2]](#ref2).
But the implementation in [[2]](#ref2) seems undocumented.

**WARING: this implementation is experimental,
even the idea is not guaranteed to be correct.**


## Source code structure and reading guide

The source code structure is identical to `typed-meta`:

- `Syntax.ml`: definition of core syntax, surface syntax and semantic values
- `MetaContext.ml`: context that maintains a global list of metas
- `Normalize.ml`: a simple untyped NBE algorithm
- `Unify.ml`: the main pattern unification algorithm with pruning
- `Typecheck.ml`: a simple bidirectional type checker
- `Pretty.ml`, `Parser.mly` and `Lexer.mll`: boring utilities
- `generalizedEtaTest.ml`: tests for the implementation. You can find some example programs here

The only file different from `typed-meta` is `Unify.ml`.



## What is and why not η-contraction

In pattern unification, arguments of a meta variable must be distinct bound variables.
But since we are working with a dependently typed system,
the predicate of "being a bound variable" is not entirely trivial.
For example, `(\x. x) y` should be considered a bound variable, too.

Fortunately, normalization can help us decide this.
If a term is β-equivalent to a bound variable,
then the normalization algorithm will normalize it to a syntactic bound variable.
So as long as we are working with normal forms, there's no need to worry about β.

Unfortunately, for η the story is not so simple.
NBE can handle η-equivalence by providing η-**expanded** normal forms,
but bound variables are η-short,
so eta expansion can only drive us away from getting a bound variable.

In pattern unification literatures,
the standard method to handle η in checking pattern condition is *η-contraction*,
which is the inverse of η-expansion: it takes `\x. f x` to `f` when `x` does not occur in `f`.
However, η-contraction is hard to implement with NBE.
Values in NBE don't support such occurence check under binder,
and we have to convert the values back to terms
and perform the η-contraction syntactically by rewriting.

Besides, η-contraction is not general enough.
There is no essential difference in handling `\x. \y. f x y` and `\x. \y. f y x`,
but η-contraction can only handle thi first one.


## Generalized η-contraction

In this part, a generalized version of η-contraction is implemented.
It can not only handle `\x. \y. f x y`, but also `\x. \y. f y x`.

To grasp the idea of the implementation,
recall *why* the pattern condition is necessary.
When we are dealing with an equation `?M ts = u`,
we want to calculate a invert substitution `ts⁻¹` such that `ts⁻¹ . ts = id`,
so that we can obtain to `?M` by applying `ts⁻¹` to `u`.

Calculating a principal inverse substitution for arbitary `ts` is impossible.
However, when `ts` is a list of distinct bound variables `xs`,
`xs⁻¹` can be easily computed: that's why we need the pattern condition.

Now, since our ultimate goal is to find the inverse substitution,
we may generalize bound variables in pattern condition to
any value that are "invertible" in some sense.
For example, `\x. f x` is invertible.
A substitution `g := \x. f x` can be inverted to `f := \x. g x`.
`\x. \y. f y x` is invertible, too.
A substitution `g := \x. \y. f y x` can be inverted to `f := \y. \x. g x y`.

So, the core of the this part is to
implement a suitable function that inverts a value.
This value inversion function can cover the case of η-contraction,
as well as other cases such as `\x. \y. f y x`.

## How to invert a value

Assume we are inverting a substitution `g := t`.
If `t` is neither a bound variable or a function, e.g. `A -> B`,
then this substitution is not invertible.
So, we only need to deal with the case where `g := \xs. f ts`,
where `f` is a bound variable and does not occur in `xs`.

Not all such substitutions are invertible, though:

- the substitution `g := \x. f a`, where `a` is a constructor, is not invertible.
Because we need to map `f` to some `\y. t` such that `t[y :=a] = g x`,
which is impossible as `x` will escape its scope.

- the substitution `g := \x. f x x`, while invertible,
don't have a principal inversion:
both `f := \x. \y. g x` and `f := \x. \y. g y` are its inversion.
So we should not invert this substitution,
otherwise principality of unification will be lost.

- the substitution `g := \x. f g x`, while invertible,
don't have a principal inversion too:
both `f := \h. \x. g x` and `f := \h. \x. h x` are inversions of it.

It turns out that, to make `g := \xs. f ts` (principally) invertible,
`ts` should satisfy some constraint highly similar to the pattern condition:

- every variable in `xs` must occur in `ts`
- `ts` should be a list of distinct bound variables
- `ts` should only contain variables in `xs`

Of course, when deciding "is this a bound variable?", we need to take βη into concern.
So we can recursively try to invert `ts`, and apply `ts⁻¹` to `xs`.
If these steps succeed, then the substitution is invertible,
with principal inversion `f := \ys. g (xs[ts⁻¹])`.

Note that the inversion operation in ordinary pattern unification cannot be reused directly, though.
Because value inversion above impose an extra constraint:
`ts` can only mention variables in `xs`.
We generalize the operation of inversion,
to allow specifying a allowed range of variables.
Variables falling outside this allowed range will be rejected.

## Implementation

To implement the above process properly,
we must also take into account NBE and de Bruijn index/level.
Refer to `Unify.ml` for more details.
The inversion operation above is implemented in `invert_spine` and `invert_value`.
The rest of the implementation is unchanged, compared to the previous part (`typed-meta`).


## References

<a id="ref1" href="https://cstheory.stackexchange.com/a/50918">[1]</a>
Swapping arguments of variables in higher-order pattern unification

<a id="ref2" href="https://github.com/AndrasKovacs/elaboration-zoo/tree/master/experiments/sigma-unification">[2]</a>
<https://github.com/AndrasKovacs/elaboration-zoo/tree/master/experiments/sigma-unification>
