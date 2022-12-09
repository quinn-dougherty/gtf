# `coq-ext-lib-mod`

A modular answer to the mighty [`coq-ext-lib`](https://github.com/coq-community/coq-ext-lib/), factoring out typeclasses.

Bob Harper, in [Modules Matter Most](https://existentialtype.wordpress.com/2011/04/16/modules-matter-most/):

> There are two fundamental problems with type classes. The first is that they insist that a type can implement a type class in exactly one way. For example, according to the philosophy of type classes, the integers can be ordered in precisely one way (the usual ordering), but obviously there are many orderings (say, by divisibility) of interest. The second is that they confound two separate issues: specifying how a type implements a type class and specifying when such a specification should be used during type inference.
