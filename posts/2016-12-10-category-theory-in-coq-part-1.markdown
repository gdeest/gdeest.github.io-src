---
title: Category Theory in Coq - Part 1
author: Gaël Deest
---

## Prolegomena

In this series, we will explore elementary notions of category theory in
the [Coq](https://coq.inria.fr) proof assistant. No prior knowledge of Coq or
category theory should be required to follow along the definitions and get a
general idea of what is going on, but some familiarity with a statically-typed
functional programming language is assumed. In particular, due to the nature of
the topic, we expect this series to be of particular interest to Haskell
programmers.

Coq being an *interactive* proof assistant, we strongly encourage the motivated
reader to get his hands dirty and try the examples by himself. This is the only
way to achieve some reasonable proficiency. Even if you have no interest
whatsoever in formal methods, you should still probably give Coq (or another
dependently-typed language) a try: delving in a much less constrained type
system will help you better understand the limitations of your favorite
functional language. Additionally, exposure to
the
[Curry-Howard isomorphism](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) between
proofs and programs, that forms the basis of modern proof assistants, will shed
a different light on your day-to-day programming tasks and make you a better
functional programmer, much like learning Haskell can help an imperative
programmer apply saner design principles in his language of choice.

## Mathematical Defintion of a Category

We start by recalling the definition of
a [category](https://en.wikipedia.org/wiki/Category_(mathematics)). Categories
are the proper framework to define and talk about composition. Simply speaking,
it consists in a class of points and arrows between those points.
Whenever an arrow starts where another ends, we can talk about their
*composition*. We sprinkle a few axioms on top of that intuition to make it a
reasonably useful mathematical theory - and that's about it !

More formally, a category $\mathcal{C}$ is defined by:

  - A class of *objects* (or *points*), denoted $\mathrm{ob}(\mathcal{C})$.
  - For each pair of objects $a,b: \mathrm{ob}(\mathcal C)$, a class of directed
*arrows* (or *morphisms*) between $a$ and $b$, written $\mathrm{hom}_{\mathcal
C}(a,b)$ (or just $\mathrm{hom}(a,b)$ when the underlying category is clear from
context). 

    If $f: \mathrm{hom}(a,b)$ is a morphism, $a$ is called its *domain* and $b$ its *codomain*.

  - An identity arrow $\mathrm{id}_{\mathcal C}(x): \mathrm{hom}(x,x)$ (or $\mathrm{id}(x)$) for each
$x: \mathrm{ob}(\mathcal C)$.
  - A composition operation, usually written $\circ$ in infix notation, defined
    between *composable* arrows. Two arrows $g$ and $f$ are deemed *composable* if
    the domain of $g$ is also the codomain of $f$. For any $a,b,c: \mathrm{ob}(\mathcal
    C)$, given a pair of morphisms $g: \mathrm{hom}(b,c)$ and $f: \mathrm{hom}(a,b)$,
    we thus have a morphism $g \circ f: \mathrm{hom}(a,c)$. 

The definition of composition might be reminiscent of the composition of
functions. That is not an accident: we can (and will) define a category whose
objects are *sets* and morphisms *functions*. In that category, composition is
just the usual composition of functions you know and love. Although that is a
good first mental model, please don't make the mistake of believing that
morphisms are always functions of some kind. In spite of its simplicity, the
notion of category is much more general than that - that is the root of its
beauty and usefulness.

In addition to the structure we just defined, categories must verify a few
intuitive axioms:

1. **Composition is associative:** Whenever $g,f,h$ are suitably composable, $$h \circ
   (g \circ f) = (h \circ g) \circ f.$$
2. **Identity is neutral wrt left and right composition:** For any objects $a,
   b$ and morphism $f: \mathrm{hom}(a,b)$, $$f \circ \mathrm{id}(a) = \mathrm{id}(b) \circ f = f.$$

## Definition in Coq

That definition can be easily translated to a Coq record:

```coq
Polymorphic Record Category: Type :=
  {
    (* Type of objects. *)
    ob: Type;

    (* Type constructor of morphisms between two objects. *)
    hom: ob -> ob -> Type;

    (* Identity. *)
    id a: hom a a;   
    
    (* Composition of arrows. *)
    comp {a b c}: (hom b c) -> (hom a b) -> (hom a c);
    
    (* Associativity of composition. *)
    comp_assoc:
      forall a b c d,
      forall (f: hom a b) (g: hom b c) (h: hom c d),
        comp h (comp g f) = comp (comp h g) f;
    
    (* Identity arrow is neutral with respect to left and right composition. *)
    id_comp_neutral:
      forall a b: ob,
      forall f: hom a b,
        (comp f (id a) = f) /\ (comp (id b) f = f)
  }.
```

That may be a bit much to swallow all at once, so let us break it down:

```
Polymorphic Record Category: Type :=
  {
```

We define a record type *Category*. Records in Coq are very similar to those
offered by Haskell, with a few subtleties we will describe as we proceed. Each
field is translated to an accessor function that allows you to extract
information without pattern-matching. As for the *Polymorphic* keyword, it
enables *universe polymorphism* for the type we are defining. If you don't have
a clue of what I am talking about, you can safely ignore it. In fact, it is not
necessary for the examples we define in this post [^1].

```
    ob: Type;
```
Here, we specify a field *obj* of type *Type*, which corresponds to the type of objects of the category.
Whenever we have a category *C: Category*, we can retrieve the type of its objects with *ob C*.

```
    hom: ob -> ob -> Type;
```

The field *hom* is a type constructor taking two elements of type *ob* and
returning the *Type* of arrows between those objects. One syntactic (but
important) remark: in this context, *ob* is not a function of type *Category ->
Type* ; it simply refers to the value of the field in the same category. So, for
any category *C: Category*, *hom C* has type: *ob C -> ob C -> Type*.

In general, the definition of a record field may depend on previously defined
fields in the same record.

```
    comp {a b c}: (hom b c) -> (hom a b) -> (hom a c);
```

This is a function field defining the composition of two composable arrows. Note
that composability is encoded in the type: there is no way to compose two
morphisms whose domain and codomain don't match. As for the variables *a*, *b*,
*c* we don't need to specify their type: it can be automatically inferred as
*ob* by Coq from the use of *hom*.

You may be confused by the position of *a*, *b* and *c* to the left of the colon
(*:*) character. It allows us to easily refer to those variables in the
remaining of the type. A more verbose but mostly equivalent way to define that
field would be:

```
    comp: forall (a b c: ob), (hom b c) -> (hom a b) -> (hom a c)
```

That weird function type is
a
[*dependent product type*](https://en.wikipedia.org/wiki/Dependent_type#Formal_definition).
It allows the return type of a function to depend on the *value* of its
arguments. Conceptually, our *comp* operation does hence take five arguments,
and not two, the first three ones defining the domains and codomains of the
composed arrows.

Finally, the curly braces around *a b c* define these arguments as implicit:
whenever possible from context, we ask Coq to infer them automatically. Coq
features many such facilities. While they may be be daunting at first and make
Coq programs hard to understand for a novice, they can greatly improve
readability.

That implicitness is limited to the rest of the definition, though. For a reason
I don't fully understand, arguments *a*, *b* and *c* are *explicit* outside that
scope.

We now proceed to define the axioms of a category:

```
    comp_assoc:
      forall a b c d,
      forall (f: hom a b) (g: hom b c) (h: hom c d),
        comp h (comp g f) = comp (comp h g) f;
```

Here, *a, b, c* and *d* are objects of type *ob* and *f, g, h* morphisms between
those objects. The definition of this axiom closely follows the one we gave
above: $$h \circ (g \circ f) = (h \circ g) \circ f.$$ In fact, we could have
defined syntactic sugar to write exactly that. For now, though, we will avoid
this kind of magic.

Notice that the *forall* keyword is the same used to define a dependent product
type. In fact, that is exactly what it is. We will come back to this in a minute.

Finally, we state that identities are neutral elements for composition:

```
    id_comp_neutral:
      forall a b: ob,
      forall f: hom a b,
        (comp f (id a) = f) /\ (comp (id b) f = f)
  }
```

## First example: the ${\rm S{\small ET}}$ Category

The category ${\rm S{\small ET}}$ where objects are sets and morphisms functions
is probably the simplest example of a category. Let us first summarise how it
maps to our definition:

- Objects have type *Set*.
- Arrows between two sets *A* and *B* are functions of type *A -> B*.
- The identity arrow of set *A* is the function that maps each element to
  itself.
- Composition of arrows is simply composition of functions.

That should be simple enough to implement. Let's start by defining the
identities and composition as separate functions:

```coq
Definition set_id (A:Set): (A -> A) := fun a => a.

Definition set_compose {A B C: Set} (g: B -> C) (f: A -> B) := fun x => g (f x).
```

So, *set_id* takes a *Set* and returns the identity function for that *Set*,
while *set_compose* takes three *Sets*, two functions between them and returns
their composition. Since the *Set* arguments can easily be inferred from the
type of functions *g* and *f*, we define them as implicit to remove
clutter. Easy enough !

Now, we have to actually prove the category axioms. We do so by definining and
proving two lemmas, *set_comp_assoc* and *set_id_comp_neutral*. The statement of
our lemmas are immediately followed by their proof, which, in this occasion, can
be automatically built for us by Coq using the *auto* tactic.

```coq
(* Composition of functions is associative. *)
Lemma set_comp_assoc: forall (a b c d: Set), forall (f: a -> b) (g: b -> c) (h: c -> d),
      set_compose h (set_compose g f) = set_compose (set_compose h g) f.
  auto.
Qed.

(* An identity function is a neutral element for left and right composition. *)
Lemma set_id_comp_neutral: forall a b: Set, forall f: a -> b,
      set_compose f (set_id a) = f /\ set_compose (set_id b) f = f.
  auto.
Qed.
```

Let us reflect a bit more on what is going on here. Stating a lemma (or a
theorem) and giving its proof is actually *exactly the same thing* as defining a
type *and* a value of that type. That's the core of the Curry-Howard
isomorphism: proofs and programs are just the same concept seen from different
viewpoints. An element: *x: T* is a proof of *T*, seen as a proposition. That's
why types and propositions can both be built with *forall*, seen in one case as
a dependent product, in the other, as the usual universal quantifier, $\forall$.
In fact, there is absolutely no difference.

Actually, instead of using *Lemma* and the tactic language, could have defined
our proof as a function taking all the variables involved in the theorem as a
arguments and returning an equality proof:

```coq
Definition set_comp_assoc: forall (a b c d: Set), forall (f: a -> b) (g: b -> c) (h: c -> d),
      set_compose h (set_compose g f) = set_compose (set_compose h g) f :=
  fun a b c d f g h  => eq_refl (set_compose h (set_compose g f)).
```

The details of that (very short) proof are not that important. I just want to
stress out that, while Coq offers a lot of syntactic sugar, the underlying
theory is just a very small, very flexible kernel where proofs and programs are
one and the same.

Well, almost the same. In Coq, there is a subtle difference between propositions
and conventional types: by construction, the type (or kind, if you wish) of a
proposition is *Prop*. This is just a nifty trick used to ensure that proofs can
be fully erased when extracting Coq programs to OCaml or Haskell[^2]. But it is
more of practical than theoretical importance.

Finally, we have all the ingredients to build our first category:

```coq
Definition SET : Category :=
  {|
    ob              := Set;
    hom             := fun a b => a -> b;
    id              := set_id;
    comp            := @set_compose;
    comp_assoc      := set_comp_assoc;
    id_comp_neutral := set_id_comp_neutral
  |}.
````

Hooray ! The @ before *set_compose* is just there to make all arguments explicit
in *set_compose* and make its type match with comp (recall that all *comp*
arguments are explicit outside the definition of the record). Other than that,
everything should be pretty obvious.

In the next parts, we will define some more interesting examples such as Kleisli
categories, and the category of categories (!), along with the corresponding morphisms:
functors !

[^1]: It will be, in the next part. Stay tuned !
[^2]: See [this paper](https://www.irif.fr/~letouzey/download/letouzey_extr_cie08.pdf) for more information.
