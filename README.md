# pruning-tutor
a tutorial implementation on an elaborator of a dependently typed language with pruning

## Overview

This is a tutorial implementation of elaborators for a simple dependently language with:

- Normalization by Evaluation (NBE)
- higher order pattern unification with *pruning*

There are two parts in this tutorial:

- `untyped-NBE` is the most basic setting. It uses an untyped NBE algorithm.
- (WIP) `typed-NBE` uses a *typed* NBE algorithm. It turns out that this has non-trivial interaction with unification.

Each part assumes basic understanding of the contents in the previous parts.
So it is recommended to read these parts in order.
The directory of each part holds a README for the technical details and source code reading guide of that part.
You can find a brief introduction of the general topic of elaboration and pattern unification below.


## Introduction

Elaboration is an important part of dependent type checking,
where source terms with a convenient surface syntax is elaborated
into a more explicit, restrictive yet simple core calculus.

Elaboration is usually type directed,
so type checking must be done during elaboration too,
which involves normalizing terms in order to compare them,
making the elaboration process very complex.

A very important concept in elaboration is *meta variables* or *existential variables*,
which are special variables that stand for some unknown expression,
and may be solved and replaced by the elaborator during type checking.
Metas are used to implement holes,
where the program can leave out some part of an expression
and let the type checker infer it automatically,
as well as functions with implicit arguments.

To solve meta variables during type checking,
it is necessary to support *unification* of terms.
For a dependently typed language, this unification process is *higher order*,
as it must take the semantic of terms (e.g. β and η equality) into account.

Unfortunately, general higher order unification is undecidable.
Fortunately though, there is a famous decidable fragment called *higher order patterns*,
where all meta variables are applied to a list of *distinct* bound variables, e.g. `?M x y z`.
In this case, equations concerning meta variables can be directly read as a definition.
For example, the equation `?M x y z = x + (y * (z + x))`
has a most general solution `?M = \x. \y. \z. x + (y * (z + x))`.

While pattern unification with various variants and extensions
have been studied extensively in the literature,
*implementing* it in a actual elaborator is a completely different story.
In research papers, the unification algorithm is usually presented as a series of rewrite rules,
which is convenient for proving properties of the algorithm,
but difficult/inefficient to implement directly.
Besides, research papers usually prefer a named term representation for convenience,
but in implementation, de Bruijn index/level may be more desirable.

Yet another layer of complexity is introduced,
by the use of *normalization by evaluation* (NBE).
Normalization by evaluation is an efficient way to evaluate and normalize terms,
it is orders of magnitude faster than small-step βη reduction with capture-avoiding substitution.
However, the interaction between NBE and pattern unification is non trivial,
and requires special cares during implementation.
