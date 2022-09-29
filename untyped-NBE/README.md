# Untyped NBE + unification with pruning

## Source code structure and reading guide

- `Syntax.ml`: definition of core syntax, surface syntax and semantic values
- `MetaContext.ml`: context that maintains a global list of metas
- `Normalize.ml`: a simple untyped NBE algorithm
- `Unify.ml`: the main pattern unification algorithm with pruning
- `Typecheck.ml`: a simple bidirectional type checker
- `Pretty.ml`, `Parser.mly` and `Lexer.mll`: boring utilities
- `PruningTest.ml`: tests for the implementation. You can find some example programs here

If you already have some experience with dependent type checking and NBE,
all files except `Unify.ml` are standard.
Core terms use de Bruijn index, and values use de Bruijn level.
It is recommended to first read `Syntax.ml` for the definition of the syntax,
then read `Unify.ml` for the unification algorithm,
referring to other modules when you are not sure about the API.

If you are not familiar with NBE and dependent type checking at all,
it is recommended to refer to some other tutorials first,
as this tutorial won't explain these concepts in detail.
My personal recommendation is part
`01-eval-closure-debruijn` and `02-typecheck-closure-debruijn` of [[1]](#ref1),
as this tutorial uses de Bruijn index/level too.
The first two chapters of [[2]](#ref2) is also a good reference
for readers seeking a more formal presentation.

## Pattern unification

A terms is said to be a *higher order pattren*,
if all meta variables in it is applied to a *distinct* list of bound variables.
Higher order unification problem of higher order patterns is decidable,
and has most general solutions.

Since we are dealing with higher order unification,
terms have a non-trivial equation theory with βη equalities.
From now on, we assume that all terms are in β-normal form.
This can be achieved by always normalizing terms before unification/after substitution.
In this tutorial NBE is used to achieve this.

In this tutorial, metas are considered globally defined functions.
For example, a meta variable `?M` defined in the context `Γ` with type `A`
is considered a global function of type `Γ -> A`.
To insert `?M` into the context `Γ`, the list of variables in `Γ` is applied to `?M`.

As in the literatures, we will call terms of the form `?M xs` *flexible*,
and other terms *rigid*.
A rigid term is a constant/constructor or a free variable
applied to a list of arguments, e.g. `A -> B` and `f x y`.

Assume that we are trying to unify two terms `t` and `u` (in β-normal form).
If `t` and `u` are both rigid, then we compare their head.
If they haev different head (e.g. `(A -> B) = (\x. t)` or `f x = g y` with `f ≠ g`),
then the problem is not solvable.
If `t` and `u` have the same head constructor, we decompose the unification problem
into smaller problems
(e.g. `\x. t = \x. u` can be reduced to `t = u`,
`f t₁ u₁ = f t₂ u₂` can be reduced to `t₁ = t₂` and `u₁ = u₂`).
After performing these reductions, we are left with three possible cases:

1. *flex-rigid*, where one of `t` or `u` is a free variable applied to arguments,
with the other being a meta variable applied to arguments.
Without loss of generality, assume `t = ?M ts` and `u = x us`.
Since we are dealing with *pattern* unification, `ts`
must be a list of distinct bound variables `xs`.
Since metas are global functions, they can only depend on their arguments.
So it must be the case that `x ∊ xs`, otherwise the problem is unsolvable.
If indeed `x ∊ xs`, we can now reduce the problem to `?Mᵢ xs = uᵢ`,
where `us = u₁, ..., uₙ` and `?Mᵢ` are fresh meta variables,
with `?M` solved to `\xs. x (?M₁ xs) ... (?Mₙ xs)`.
To make sure that the algorithm terminates,
we must also check that `?M` does not occur in `us`,
otherwise the unification algorithm may loop forever.

1. *flex-flex*, same meta, where `t = ?M xs` and `u = ?M ys`.
In this case, `?M` can only depend on its `i`-th arguments for those `i`s such that `xᵢ = yᵢ`.
For example, if we have `?M x y = ?M x z`, and `?M = \$0 \$1. body`,
then `$1` must not occur in `body`, because otherwise the `$1` occurence in `body` will be
unequal for `?M x y` and `?M x z` (`y` v.s. `z`).
Let `zs` be the list of variables that are "safe" to depend on,
we can solve this equation by `?M = \xs. ?M' zs`, where `?M'` is a fresh meta variable.

1. *flex-flex*, different meta, where `t = ?M1 xs` and `u = ?M2 ys`,
with `?M1` and `?M2` being different meta variables.
Following a similar argument from the previous case,
`?M1` and `?M2` can only depend on the variables in `xs ∩ ys`.
Let `zs = xs ∩ ys`, then we can solve `?M1 xs = ?M2 ys` by
`?M1 = \xs. ?M' zs` and `?M2 = \ys. ?M' zs`, where `?M'` is a frehs meta variable.

In summary, the above four cases make up the following rules,
of the form `e -> (E, σ)`, where `e` is a single equation, `E` is a list of equations
and `σ` is a meta variable substitution:
    f ts = f us -> ({tᵢ = uᵢ}, ∅ )
        where f is a constructor, a constant or a free variable

    ?M xs = x us or x us = ?M xs -> ({ ?Mᵢ xs = uᵢ }, [?M := \xs. x (?M₁ xs) ... (?Mₙ xs)]
        where ?M does not occur is us
              ?Mᵢ are fresh meta variables
              x ∊ xs

    ?M xs = ?M ys -> (∅ , [?M := \xs ?M' zs])
        where zs = { xᵢ | xᵢ = yᵢ }
              ?M' is a fresh meta variable

    ?M1 xs = ?M2 ys -> (∅ , [?M1 := \xs ?M' zs, ?M2 := \xs. ?M' zs])
        where ?M1 ≠ ?M2
              zs = xs ∩ ys
              ?M' is a fresh meta variable

    otherwise -> fail

These four rules, together with the decomposition rules,
make up a complete specification of a higher order pattern unification algorithm.

## From specification to algorithm

The specification above can be proved to be correct, complete and terminating.
However, it is hard to implement directly, and may be very inefficient in practice.
For example, in the flex-rigid case, many new fresh metas are generated at each step.

Following [[3]](#ref3),
we want to transform the rewrite rules in the specification to a practical unification *algorithm*.
Assume we have a equation `?M xs = t` to solve, where `t` is not of the form `?M ys`
(so we are in either a flex-rigid case or a flex-flex case with different metas).
Instead of generating a lot of fresh metas and new equations,
we want to solve this equation in one single big step.

Assume `?M : Γ -> A` and the equation happens in context `Δ`,
now `xs` can be viewed as a substitution `Δ |- xs : Γ`, and `?M xs` and `t` have type `A[xs]`.
Note that this view of `xs` as an explicit substitution is compatible with de Bruijn index/level too.
Since `xs` is a list of distinct bound variables,
we know that `xs` is injective, and has an inverse `Γ |- xs⁻¹ : Δ`.
Now, applying `xs⁻¹` to `t`, we can obtain a term `Γ |- t[xs⁻¹] : A`,
and solve `?M` with `\Γ. t[xs⁻¹]`.

There are two extra things to note here.
First, `xs` may not cover all variables in `Δ`,
so `xs⁻¹` is only a *partial* substitution, and applying it to `t` may fail,
which indicates that some variables in `t` may escape its scope through `?M`.
For example, the equation `?M x y = z` should not be solvable,
because `?M` can only depend on `x` and `y`.
Second, we should also perform the occurence check when applying the partial substitution.
If we encounters the meta variable `?M` during the application of `xs⁻¹`,
the algorithm should fail due to recursive occurence of `?M`.

Applying the ideas above, one can obtain a very simple implementation of pattern unification.
`03-holes` of [[1]](#ref1) is one such implementation.
The implementation here is also based on this simple implementation,
but with an extra improvement: pruning.

## From flex-flex to pruning
The above simple algorithm is not equivalent to the pattern unification rewrite system.
In particular, it fails to handle the flex-flex case properly.
Assume we have a equation `?M1 x y = ?M2 x z`,
the inverse of `x, y` is `x := $0, y := $1`,
but applying it to `?M2 x z` fails because `z` is not in the domain of the partial substitution.
If we go the other way around and apply the inverse of `x, z` to `?M1 x y`,
the algorithm will still fail due to `y` not belonging to `x, z`.

Before diving into how we can solve this problem with pruning,
let's first inspect the relation between the inverse substitution operation
and the original rewrite rules.
Actually, the operation of computing `t[xs⁻¹]` exactly corresponds to
solving an equation `?M' xs = t`, with `?M'` not explicitly created.
During the computation of `t[xs⁻¹]`, we may go through constructors and free variable applications,
which corresponds exactly to a flex-rigid step in the rewrite rules.

Now, what if we are trying to compute `(?M ys)[xs⁻¹]` for some flexible terms?
If we follow the rewrite rules strictly, a flex-flex step with intersection should be performed here.
However, in the näive implementation above,
we simply treat `?M` as a free variables and apply `xs⁻¹` recursively on `ys`,
which is the root of problem.

So, to improve the algorithm and follow the rewrite rules strictly,
we should perform an intersection as in the flex-flex case,
when we encounter a flexible term during applying a partial substitution.
This improvement is called *pruning*,
as it will "prune away" dangerous variables from the arguments of a meta variable,
so that the partial substitution will succeed.

But how? Here, in contrast to `05-pruning` of [[1]](#ref1),
where pruning operations are implemented on their own,
I propose thinking in terms of *explicit substitution*,
and derivate the pruning operations from the basic idea, reusing partial substitution operations.

Ignore occurs check for a while, and assume we are computing `(?M ys)[xs⁻¹]`.
Assume `Γₓ |- xs⁻¹ : Γ`, `?M : Γₘ -> A` and `Γ |- ys : Γₘ`.

1. First, we should ensure that `ys` is a list of distinct bound variables
and hence satisfies the definition of higher order patterns.
We can achieve this by computing the inverse of `ys`, `Γₘ |- ys⁻¹ : Γ`.

2. Recall that in the flex-flex case of the rewrite system, we need to compute `xs ∩ ys`.
Now that we have `xs⁻¹` and `ys⁻¹`, we can simply take the intersection of their domain.

3. If `ys` is included in `xs`, then there is no need to prune `?M`,
and we can leave `?M` as is and apply `xs⁻¹` on `ys` directly.

1. If `ys` is not included in `xs`, we must prune away some variables from `ys`.
First, let's allocate a fresh meta variable `?M'`,
we should set `\Γₘ . ?M' zs` for some `zs`, and the main difficulty lies in computing `zs`.
This is particularly complex when we are using de Bruijn index/level.

1. First, let's figure out what the type of `?M'` should be.
`?M'` should have type `Γₘ' -> A[wk]`, where `Γₘ'` is `Γ` with variables not in `xs` pruned away,
and `Γₘ |- wk : Γₘ'` is the weaking substitution.

1. Under `Γₘ'`, `zs` is simply all the variables/indicies/levels is `Γₘ'` and is easy to compute.
Let this list of variables be `zs'`

1. Now, to obtain `zs` in `?M := \Γₘ. ?M' zs`, we should lift `zs'` to `Γₘ`.
This can be achieved by applying `wk` to `zs'`, reusing the partial substitution operation.

1. Now that we have obtained `zs` and solved `?M`, we should consider what the result of
`(?M ys)[xs⁻¹]` should be.
Since we have already solved `?M` with `v = \Γₘ. ?M' zs`,
we can reuse the evaluation mechanism and partial substitution operation,
applying `xs⁻¹` to `v ys` directly.
Since "bad" variables in `ys` are already pruned away by `v`,
we know that there's no need for pruning in `(v ys)[xs⁻¹]`,
and its computation must fall in the case of step (3.) above,
hence this recursive computation won't loop forever.

For the detailed index/level arithmetic,
and how to compute the weakening substitution, etc.,
refer to `Unify.ml`.


## Integration with elaboration

I have explained the pattern unification algorithm in details above.
However, there are some extra cares to take when trying to integrate it with an elaborator
for a dependently typed language.

First, what should the unification operates on, in a NBE setting: core terms or values?
Here, the unification algorithm itself operates on values,
for easy semantic operations and normalization.
However, some operations, such as applying a partial substitution,
will convert values back to core terms.
In this case, the resulting core terms may need to be evaluated back to values again.
See `Unify.ml` for more details.

Second, local `let` definitions have many non-trivial interactions with unification.
Assume we are in a context with local `let`: `Γ = x : A, y = t, z : B`.
Assume that we are type checking a hole in `Γ`.
We have created a fresh meta `?M`, which is a globally defined function.
Now we need to apply `ᴦ` to `?M` to obtain a well-typed term in `Γ`.
But the defined local variable `y` should *not* be applied to `?M`.
So we should apply only `x` and `z` to `?M`.


## References

<a id="ref1" href="https://github.com/AndrasKovacs/elaboration-zoo">[1]</a>
<https://github.com/AndrasKovacs/elaboration-zoo>

<a id="ref2" href="https://www.cse.chalmers.se/~abela/habil.pdf">[2]</a>
Normalization by Evaluation, Dependent Types and Impredicativity

<a id="ref3" ref="https://ieeexplore.ieee.org/document/287599">[3]</a>
Functional unification of higher-order patterns
