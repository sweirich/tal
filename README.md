An implementation of a type-preserving Compiler, derived from the paper

[From System F to Typed Assembly Language](https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf)
by Morrisett, Walker, Crary, Glew

I was inspired to implement this paper while preparing for
[Papers We Love](https://www.youtube.com/watch?v=Epbaka9uTQ4). 

The implementation includes all passes described in the paper:

* F ==> K   (Typed CPS conversion)
* K ==> C   (Polymorphic closure conversion)
* C ==> H   (Hoisting, reuses the C language)
* H ==> A   (Allocation)
* A ==> TAL (Code generation)

Each language (F, K, C, A, TAL) is defined in the corresponding source
file. These implementations include the abstract syntax, small-step
operational semantics, and type checker for the languages. The file
[Util.hs](src/Util.hs) contains definitions common to all implementations.

The compiler itself is in the file [translate.hs](src/translate.hs).  To run
the compiler, load this file into ghci and try out one of the sample programs from [F.hs](src/F.hs).

In particular, you can try

     Translate*> printM $ compile F.sixfact

to see the TAL output for the factorial function applied to six.

If you would like to compile and then run this function you can try:

     Translate*> test F.sixfact

-------------------------------------------------------------------------