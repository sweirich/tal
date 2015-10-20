An implementation of a type-preserving Compiler, derived from the paper

[From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
by Morrisett, Walker, Crary, Glew

So far, the implementation only includes the first two passes:

* F ==> K   (Typed CPS conversion)
* K ==> C   (Polymorphic closure conversion)

