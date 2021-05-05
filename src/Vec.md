## Implementing the Gram-Schmidt method in Idris2: Take 1
This is a tutorialish implementation of the Gram-Schmidt Algorithm
as found [here](https://github.com/fog-hs/gram-shmidt)
in Idris2. Readers are assumed to be familiar with
languages with Haskell-like syntax in order to follow.
Everything else, I'll try to explain on the go.

This is a literate Idris2 file, so we first declare our
module name and imports. For length indexed lists of values,
we use `Vect` from `Data.Vect`. This comes with a lot of
interfaces (comparable to typeclasses in Haskell) like `Functor`,
`Applicative`,`Traversable`, `Foldable`, and `Zippable` already
implemented.

```idris
module Vec

import Data.List
import Data.Vect
```

Before we begin: You can load this file into an Idris2
REPL session. This will allow us to experiment with some of the
features Idris2 provides. In order to do so, run the following
from the root directory of this repository:

```
idris2 --find-ipkg src/Vec.md
```

If you'd like to use your arrow keys to scroll through previous
commands (the Idris2 REPL does not provide this functionality),
you can wrap the command above in a call to `rlwrap` (if you
have that installed, that is):

```
rlwrap idris2 --find-ipkg src/Vec.md
```

### Dot Product
Idris2 has an exponentiation operator `(^)` in `Data.Monoid.Exponentiation`
in `contrib`, but not as part of the `Num` interface. I think, there
is an open issue about this, though.

Anyway, we write our own squaring function.

```idris
public export
square : Num a => a -> a
square x = x * x
```

Like in Haskell, we can define a constrained function with
the `Num a =>` syntax. Internally, Idris2 uses the following
type for `square` (and we could ourselves have declared
`square`s type this way), and before we move on, I'd like to quickly
explain what's going on here:

```
square : {0 a : Type} -> {auto _ : Num a} -> a -> a
```

Let's break this down a bit. The first argument `{0 a : Type}`
is an *implicit* argument of type `Type`. Implicit meaning,
that in most circumstances, Idris2 can infer it automatically
from the context in which the function is called. The `0`
quantifier means, that this argument is guaranteed to be erased at runtime,
so it is only relevant during type checking.
You can look at a function's implicit arguments in the
REPL by using the `:ti` command:

```
Vec> :ti square
Vec.square : {0 a : Type} -> Num a => a -> a
```

The second argument `{auto _ : Num a}`, which came from the `Num a =>`
syntactic sugar, is an unnamed (since the name is just an unserscore)
*auto implicit* argument. Here we ask Idris2 to automatically search
for a value of this type whenever we invoke `square`. In Haskell
this is called *typeclass resolution* and likewise in Idris2 *interface resolution*,
but in Idris2 it is also often called *proof search*, since it
does not only work for interfaces but for (simple) proofs in general.

We can now implement dot products:

```idris
public export
dot : Num a => Vect n a -> Vect n a -> a
dot xs ys = sum $ zipWith (*) xs ys
```

Again, we quickly look at the fully expanded type of `dot`:

```
Vec> :ti dot
Vec.dot : {0 n : Nat} -> {0 a : Type} -> Num a => Vect n a -> Vect n a -> a
```

So, this time we have two implicit erased arguments: `n` and `a`, and as can
be seen, they do not always need to be of type `Type`.
`n` corresponds to the length of the vectors, and here we used
it as a compile time proof, that the vectors are of the same length.

The implementation is simple: We multiply the elements of the
two vectors in pairs using `zipWith (*)` and sum up the results.

### Direction and Projections

In the remainder of this introduction, we are mostly
interested in vectors with `Double` entries. For those,
we can provide a type alias. In Idris2, there is no special
syntax for type aliases. They are just ordinary functions,
which calculate a type from their input:

```idris
public export
Vec : Nat -> Type
Vec n = Vect n Double
```

Normalizing vectors now seems straight forward:

```idris
public export
norm : Vec n -> Double
norm = sqrt . sum . map square

public export
scale : Num a => a -> Vect n a -> Vect n a
scale a = map (a *)

public export
direction : Vec n -> Vec n
direction xs = scale (1 / norm xs) xs
```

Note, however, that `direction` is a rather unsafe operation
as it contains a potential division by zero. We will look at
how to make this more safe in a later post.
From the above, we can derive two more unsafe functions:

```idris
public export
project : Vec n -> Vec n -> Vec n 
project xs ys = ((xs `dot` ys) / square (norm ys)) `scale` ys

public export
angle : Vec n -> Vec n -> Double
angle a b = (a `dot` b) / ((norm a)*(norm b))
```

### Gram-Schmidt, take 1

We are now ready to actually implement the *Gram-Schmidt*
procedure.

```idris
public export
gramSchmidt : List (Vec n) -> List (Vec n)
gramSchmidt = reverse . foldl (\ys,x => f x ys :: ys) Nil
  where g : Vec n -> Vec n -> Vec n -> Vec n 
        g x a b = zipWith (-) a (project x b)

        f : Vec n -> List (Vec n) -> Vec n
        f x = direction . foldl (g x) x
```

Note that, unlike in Haskell, we have to give explicit types
for utility functions `g` and `f`, as type inference does
not work for the general case in dependently typed langauges.
While this makes the implementation somewhat more verbose,
it can at the same time make it easier to understand
what's going on.

We can now give this a try in the REPL:

```
Vec> gramSchmidt [[1,2],[3,4]]
[[0.4472135954999579, 0.8944271909999159], [0.8944271909999157, -0.44721359549995837]]
Vec> map norm $ gramSchmidt [[1,2],[3,4]]
[0.9999999999999999, 1.0]
```

### A `Num` implementation for `Vect n a`

It would be quite convenient, if we could have a `Num` instance
for vectors holding numbers. Let's give it a spin:

```
Num a => Num (Vect n a) where
  (+) = zipWith (+)
  (*) = zipWith (*)
```

That was easy. But how to implement `fromInteger`? Well,
for a vector of length 2, we expect `fromInteger 3` to
yield `[3,3]`. There is a function for this in `Data.Vect`
called `replicate`. But `replicate` takes the desired length
of the vector as an explicit argument. We can't do that
in our `Num` instance, but we can do something else: We
can request the length of the vector as an unerased implicit
argument

```idris
public export
{n : Nat} -> Num a => Num (Vect n a) where
  (+) = zipWith (+)
  (*) = zipWith (*)
  fromInteger = replicate n . fromInteger
```

The `{n : Nat}` implicit argument states, that Idris2 needs
to be able to infer `n` from the context (no surprises here,
as `n` would be an implicit argument for this declaration
anyway), but that in addition, `n` will (and must not!) be
erased at runtime (note the missing `0`). This allows us to
refer to `n` in the declaraction's body, as can be
seen in the implementation of `fromInteger`.

If we try this in the REPL, Idris needs some help to correctly
infer the types. Prelude function `the` is incredibly useful
for this. It allows us to explicitly state the type of a value:

```
Vec> [1,2] + the (Vect 2 Int) [3,4]
[4, 6]
Vec> [1,2] + the (Vect _ _) [3,4]
[4, 6]
```

In the first example, we specify the full type: `Vect 2 Int`. In the
second, we use underscores where we think Idris should be able
to figure out the correct values on its own (it will default
the value type to `Integer` in this case).

In order to use `fromInteger`, we need to specify the length explicilty,
or make sure, Idris can infer it from the context:

```
Vec> the (Vec 4) $ fromInteger 10
[10.0, 10.0, 10.0, 10.0]
Vec> the (Vec _) [1,2] + fromInteger 0
[1.0, 2.0]
```

Other numeric implementations come without additional obstacles.
The unerased implicit will always be present, however, as all
these interfaces require an implementation of `Num`:

```idris
public export
{n : Nat} -> Abs a => Abs (Vect n a) where
  abs = map abs

public export
{n : Nat} -> Neg a => Neg (Vect n a) where
  negate = map negate
  (-)    = zipWith (-)

public export
{n : Nat} -> Integral a => Integral (Vect n a) where
  mod    = zipWith mod
  div    = zipWith div

public export
{n : Nat} -> Fractional a => Fractional (Vect n a) where
  recip = map recip
  (/)   = zipWith (/)
```

### Increasing our functions' safety

Function `direction` is non-total, as in case of a zero-length
vector we divide by zero. We will fix this now. First,
we define a safe division function:

```idris
public export
posDiv : (x : Double) -> (y : Double) -> {auto 0 _ : y > 0 = True} -> Double
posDiv x y = assert_total $ x / y
```

Again, we will digest this step by step. The `(y : Double)` syntax
allows us to give names to type arguments, either for documentation,
or, because it allows us to refer to these named arguments
later on the type. We need to do this here, since we ask Idris
for an erased proof (quantity `0`!), that `y` is a positive floating
point number: `{auto 0 _ : y > 0 = True}`.

Let's try this in the REPL:

```
Vec> 10 `posDiv` 2
5.0
Vec> 10 `posDiv` 0
Error: Can't find an implementation for intToBool 0 = True.
```

Note, that in the implementation of `posDiv` we are using `assert_total`:
This is used to manually force Idris to believe that a function is indeed
total. This is often necessary when we are dealing with primitive
types (`Double` is such a primitive type), about the implementation of
which Idris does know nothing. Ideally, Idris would provide a minimal
set of such total functions (and also laws for working with primitives)
itself, but we are not there yet.

We are now ready to write a total version of `direction`:

```idris
public export
safeDirection : (xs : Vec n) -> {auto 0 _ : norm xs > 0 = True } -> Vec n
safeDirection xs = scale (1 `posDiv` norm xs) xs
```

In the REPL:

```
Vec> safeDirection [2,3]
[0.5547001962252291, 0.8320502943378437]
Vec> safeDirection [0,0]
Error: Can't find an implementation for ...
```

The error we get is quite ugly, but it actually is showing us exactly what
Idris is trying to calculate.

### Working with proofs

People new to Idris might now be under the impression, that in
general we use auto implicit arguments whenever we expect a precondition
to hold for a function, and that Idris will then provide
these proofs for us automagically. This only holds for rather simple
proofs, where the steps to perform the proof search are pretty
clear. In other circumstances, we have to provide proofs manually,
and here I'll give some more details, how this is done.

#### (WIP) Types as propositions, programs as proofs

This section is work in progress. Please come back later.

In type theory, a type can be considered to be a logical
proposition, and a total (= provably terminating) implementation
of that type is a proof that the proposition holds.
We will look at several examples.

The first thing we'd like to show is, that we can always
extract a value from a vector of non-zero length.

```idris
public export total
vectHead : Vect (S n) a -> a
```
 
Note, how we can specify that a vector is of non-zero length,
by using pattern match on its length index. Given the additional
implicit arguments `{0 n : Nat}` and `{0 a : Type}`, the proposition
reads as follows: For all natural numbers `n` and for all types `a`,
given a vector of `a`s of length `S n`, there is a value of type `a`.
Now, we proof that this proposition holds by implementing `vectHead`:

```idris
vectHead (v :: _) = v
vectHead Nil impossible
```

This is a simple pattern match, but the second clause is special:
In order to make sure that the pattern match covers all possible
data constructors, we have to include the case of the empty vector `Nil`.
But this clause is impossible, since `Nil`s type is `Vect Z a`, cannot
be unified with the given type `Vect (S n) a`. We therefore tell Idris
that we think this clause to be impossible and Idris will answer with
a type error if it can't verify this.

Strictly speaking, it is not necessary to include the `impossible`
clause. Idris can often figure this out itself during coverage
checking. Yet, there are pathological cases where this doesn't work,
therefore I consider it to be good practice to include these clauses in general.

Now, we will come up with something a bit more involved.
We'd like to somehow show - at the type level - that a vector of
doubles is not of zero norm. We can use a type for this:
