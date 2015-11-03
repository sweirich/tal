An implementation of a type-preserving Compiler, derived from the paper

[From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
by Morrisett, Walker, Crary, Glew

I was inspired to implement this paper while preparing for
[Papers We Love](https://www.youtube.com/watch?v=Epbaka9uTQ4). 

So far, the implementation includes the first four passes:

* F ==> K   (Typed CPS conversion)
* K ==> C   (Polymorphic closure conversion)
* C ==> H   (Hoisting, reuses the C language)
* H ==> A   (Allocation)
