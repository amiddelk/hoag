hoag
====

This package provides an EDSL for building _data flow graphs_ based
on higher-order _attribute grammars_.
The nodes of the graph are organized in a _tree_, and the data flow defined
via functions (_rules_) between _attributes_ of the nodes.

The formalism and the implementation in this package features:
* Define data flow in a hierarchically structured fashion.
* Incremental definitions: additional attributes and rules can be given,
  and existing rules can be refined.
* Implicit topdown and bottomup data flows; the latter case for monoids.
* The data flow is defined locally as functions between attributes of a
  node and those of its parent and children. A global data flow is
  derived automatically.

The DSL compiles into a monadic program representing the construction of
the graph via explicit fork/join-style combinators. We provide a trivial
Identity and an IO instance (called "Fiber"). The former provides an implicit
representation of the graph based on lazy evaluation, and the latter emulates
lazy evaluation. Additionally, we provide a more explicit representation
with explicit batchable effects (called "Resumption").

See _Why Attribute Grammars Matter (The Monad.Reader, Issue 4)_ by
Wouter Swierstra for a general introduction to attribute grammars
in relation to functional programming.


Known restrictions:
* Attribute types are monomorphic. There is no generialization/instantiation of
  the attribute types of nonterminals.
* The structure of the grammar is collected in a single step, thus intermediate
  representations are not accessible for defining the structure of the grammar
  itself (i.e. for generic programming).
