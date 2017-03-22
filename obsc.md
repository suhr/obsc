Title: “␣;”: A Simply Arited Concatenative Language

<div class="abstract">This article attempts to formalize “function composition instead of function application” definition of concatenative languages by introducing <code>␣;</code>, a simple concatenative language based on two operations: composition (<code>f g</code>) and parallel concatenation (<code>f ; g</code>). Assuming that all function have fixed arities, we define concrete semantics of the language and show how to make it Turing-complete.</div>

Among lesser-known programming languages, there're beautiful ones, that change the way you think about programming, and let you express things in a way you couldn't express before.

Concatenative languages allow you to write code in a way, hard or impossible in other languages (except, maybe, FP/FL). A program written in these languages can be readable without having *any* variables. Concatenative languages represent data flow in a simple and intuitive way, without requiring “`.`”, “`(.) . (.)`”, and other cryptic operations. And they achieve that not by complexy, but by simplicity.

Typical code in a concatenative language looks like this:

```factor
USING: io kernel sequences
http.client xml xml.data xml.traversal ;

"http://factorcode.org" http-get nip string>xml
"a" deep-tags-named
[ "href" attr ] map
[ print ] each
```

This code is very similar to unix pipelines, but much more powerful. Fuctions can have any input and output arities, and combinators allow higher order programming.

Concatenative languages are underresearched. Most of them rely on ad-hoc tricks with stack rather then any kind of theory. Can we do better? This article tries to make a step in this direction.

## What is a concatenative programming language?

In a typical concatenative language, a program is a sequence of *words* that acts on *stack* by taking first n values from the top of the stack and replacing them by m values (n, m ≥ 0). For example, `1 3 5 * +` is evaluated like this:

|     Code    |  Stack  |
|-------------|---------|
| `1 3 5 * +` | (empty) |
| `3 5 * +`   | `1`     |
| `5 * +`     | `1 3`   |
| `* +`       | `1 3 5` |
| `+`         | `1 15`  |
| (empty)     | `16`    |

To provide higher order programming, quotations and combinators are used. A quotation is a sequence of words enclosed in square brackets, and combinators are words that take quotation from the stack to use it in some way. For example, `[ print ] each` takes a list from the stack and runs `print` on each element of the list.

While this kind of evaluation is pretty imperative, there're several *functional* models of concatenative languages.

In the first model, a program is a compostiton of functions that pass stack to each other. So, `1: S -> S 1` is a function, `*: S a b -> S (a * b)` and `+: S a b -> S (a + b)` are also functions. And compositions `1 3 5: S -> S 1 3 5` and `* +: S a b c -> S (a + b*c)` are functions too.

[Joy][joy] is a language using this model.  This model is closely related to combinatory logic, see [The Theory of Concatenative Combinators][concombs].

While this is a powerful model, it is probably *too* powerful. For example, static type checking in not a simple problem in this model, so all using this model languages are dynamically typed.

The model used in [Enchilada][enchilada] language is called term rewriting. There's no stack, a program is a sequence of terms, and evaluation is rewriting terms into other terms. For example, in this model `1 3 5 * +` is evaluated like this:

```
1 3 5 * +    → (* rule)
1 15 +       → (+ rule)
16
```

The implementation of Enchilada is quite complex, and the language seems to be also dynamically typed.

In the third model there's also no stack, and a program is a generalized composition of functions. To see what it means, let's look at ordinary function composition first.

For two functions `f` and `g`, there is a function `g . f` called *composition* of `f` and `g`, defined as `(g . f)(x) = g(f(x))`. Translated to ANF, expression `g(f(x))` looks like this:

```
let a = x in
  let b = f(a) in
    g(b)
```

But that's exactly what `x f g` is doing in a concatenative language! Except of using stack instead of variables.

`1 3 5 * +` can be represented as

```
let a = 1 in
  let b = 3 in
    let c = 5 in
      let d = (*)(b, c) in
        (+)(a, d)
```

ANF for `(+)(1, (*)(3, 5))` is basically the same up to constant definition order.

There's a more visual way to think about it. Let we have an expression `2 2 * 3 3 * +`. Then:

<table class='flow'>
<tr><td><code>2</code></td><td><code>2</code></td><td><code>3</code></td><td><code>3</code></td></tr>
<tr><td class='open'>↓ <code>2</code></td><td class='open'>↓ <code>2</code></td><td class='open'>↓ <code>3</code></td><td class='open'>↓ <code>3</code></td></tr>
<tr><td colspan='2'><code>*</code></td><td colspan='2'><code>*</code></td></tr>
<tr><td class='open' colspan='2'>↓ <code>4</code></td><td class='open' colspan='2'>↓ <code>9</code></td></tr>
<tr><td colspan='4'><code>+</code></td></tr>
<tr><td class='open' colspan='4'>↓ <code>13</code></td></tr>
</table>

[Kitten][kitten] is a languages using this model, and so is `␣;` (the language this article is about). In fact, `␣;` aims to be the simpliest language with this semantics.

Unlike stack model, generalized composition model requires knowing arities of functions *before* evaluation. This leads us to a very important restriction.

## Simply arited concatenative languages

By analogy with simply typed languages, a concatenative language is called *simply arited* if every function has only one input and output arity.

Note, that we differentiate *arity* and *typing*. They are two different concepts, and while static typing require at least some restrictions on arity, a simply arited language can be both statically or dynamically typed.

This is a pretty hard restriction. For example, you can no longer use combinators described in [TCC][concomb], you need at least `n` different functions to reorder `n` elements on the stack, and in fact, simply arited concatenative languages are probably not even Turing-complete without additional data structures! But it makes code analysis much simplier.

Let's write some arity equations for `f g`. The input arity of `f g` should be not less, than arity of `g`. But in `f g`, input arity of `g` can be bigger than output arity of `f`, so `f g` would need additional $\operatorname{Ar_{in}}(\texttt g) - \operatorname{Ar_{out}}(\texttt f)$ arguments. Applying the same reasoning to output arity of `f g`, we get:

$$
\operatorname{Ar_{in}}(\texttt{f g}) = \operatorname{Ar_{in}}(\texttt f) + \max (0, \operatorname{Ar_{in}}(\texttt g) - \operatorname{Ar_{out}}(\texttt f)) \\
\operatorname{Ar_{out}}(\texttt{f g}) = \operatorname{Ar_{out}}(\texttt g) + \max (0, \operatorname{Ar_{out}}(\texttt f) - \operatorname{Ar_{in}}(\texttt g))
$$

A better algebraist could also write arity equaltions for `f g h`. But I'm not going to, with arity equaltions for `f g` we already can derive arity of complex expressions.

So, we can check arities of expression, and there's a straightforward way to translate expressions into ANF. Time to introduce a concept that will make our language much more powerful.

## Parallel concatenation (`;`)

How do we write a fuction, that takes `a b c d` and computes $ab + cd$? Usually, concanenative language solve this problem by juggling the stack with functions like `swap`, `over`, `dup`, `drop`, `nip` and others, or use special combinators like `bi`. But for general manipulation of $n$ inputs you need at least $n$ different functions. The same holds for combinators, in a simply arited concatenative language you can't have one `bi` combinator, for each $n$ and $m$ you'll need a sepatate `bi_n_m` combinator.

So we need something else. It finds out, there's a simple and powerful way to deal with this problem.

Let `f: a1 a2 ... an -> x1 x2 ... xN`, `g: b1 b2 ... bm -> y1 y2 ... yM` be some function. Parallel concatenation of functions `f` and `g` is a function `f ; g` with input arity $n + m$ and output arity $N + M$, such as `a1 a2 ... an b1 b2 ... bn (f ; g)` returns `x1 x2 .. xN y1 y2 ... yN`.

In stack terms, `f ; g` takes $n + m$ elements from the stack, then applies `f` to the first $n$ elements and `g` to the last $m$ elements in parallel. For example, `2 2 3 3 (*) ; (*) +` squares two and three and sums the results.

Now consider substitution functions like `a b c -> b a c`, or `x y -> y`, or `y z -> z z y`. It finds out, any of them can be built from only three basic functions.

**Proposition:** every substitution function can be constructed from `dup`, `drop` and `swap`.

⏵ Indeed, let's define `id` as `dup drop`. For any n, we can define `a1 ... an -> a1 a1 ... an` function as `dup ; id ; id ; ... ; id` and `a1 a2 ... an -> a2 ... an` as `drop ; id ; id ; ... ; id`. Also, we can swap any two inputs with `swap ; id ; id ; ... ; id`.

Since every substitution can be created by multiplying some inputs, removing some other inputs and permutating the result, any substitution function can be indeed constructed using only `dup`, `drop` and `swap`. ⏴ 

So `;` operation makes our language much more powerful. It also allows us to introduce *infix notation*:

- ``f `h` g`` → `f ; g h`
- ``f `h` `` → `f ; id_n h`, where $n = \max (0, \operatorname{Ar_{in}}(\texttt h) - \operatorname{Ar_{out}}(\texttt f))$
- `` `h` g`` → `id_m ; g h`, where $n = \max (0, \operatorname{Ar_{in}}(\texttt h) - \operatorname{Ar_{out}}(\texttt h))$

This is a syntax of unreasonable expressiveness. Sum of products? It's just `(*) + (*)`. Mean value? `sum / length`. In [Why Concatenative Programming Matters][matters], there's a good example of expression that is hard to write in an ordinary concatenative programming language:

$$f(x, y, z) = y^2 + x^2 - |y|$$

The solution showed there is utterly horrible: `drop dup dup × swap abs rot3 dup × swap − +`. Another solution is `drop [square] [abs] bi − [square] dip +` – much better, but still ugly.

In our notation, it's just `drop dup (^2) + (^2) - abs`. Simple, readable, beautiful.

What about something more complex, like [coordinate rotations](https://en.wikipedia.org/wiki/Rotation_matrix)? No problem:

```
def rotate: _ _ _ -> _ _
    3dup x' ; y' where
        x' = swap over (* cos) - (* sin)
        y' = swap over (* sin) - (* cos)
```

The programming is finally liberated from von-Neumann style, but almost no readability is lost.

## Towards Turing-completeness

### Lists

TODO: `list`, `::`, `behead: list -> x xs`

### Combinators

### Recursion

TODO: recursion combinator `rec: _ ( _ bool -> _ ) -> _`

### A small base

## References

[joy]: http://www.kevinalbrecht.com/code/joy-mirror/joy.html
[kitten]: http://kittenlang.org/
[concombs]: http://tunes.org/~iepos/joy.html
[enchilada]: http://www.enchiladacode.nl/
[matters]: https://evincarofautumn.blogspot.com/2012/02/why-concatenative-programming-matters.html
