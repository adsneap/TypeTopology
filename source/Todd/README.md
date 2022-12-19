# Agda formalisation library

This is a work-in-progress Agda formalisation of the mathematical
content in the paper *Towards an API for Searchable Real Numbers*
submitted to *PLDI 2023*.

Much, but not all, of the content of the paper is formalised here
in constructive type theory, in order to provide a computational
bridge between our 'on paper' mathematical work and our Java API.

This avenue of work is nascent, but the idea is that, ultimately,
everything computable in the Java API will derive directly from
constructive proofs in this Agda formalisation. Of course, the
derived Agda programs will be (much) slower than the Java code,
but they will show that our search algorithms on ternary Boehm
encodings are directly related to the underlying mathematics
taking place on the real numbers.

## Overview and relationship to paper

The formalisation library is built in Martin Escardo's Agda
library `TypeTopology`, which formalises a huge portion of
mathematics in constructive, univalent type theory. Its approach
is compatible with that of the HoTT book.

### Main files

The file `TernaryBoehmReals` defines the type of ternary Boehm
reals that the paper/API uses for searching real numbers. The
type is defined directly, rather than by relationship to
sequences on variable-width/specific-width ...

The file `FunctionMachinery` defines types for sequences on
variable-width and specific-width interval encodings as in the
paper's Section ??. ...

The file `TernaryBoehmRealsSearch` combines the two files above
to formalise how ternary Boehm encodings can be used to search
encodings of functions on the mathematical real space. It gives
the definition of a searchable type and ...

### Supplmentary files

The file 'Prelude' includes a variety of definitions and lemmas
that are needed for our work but are not in `TypeTopology'. This
includes ...

The file `DyadicReals` defines the type of dedekind real numbers
using dyadic rational numbers. ...

The file `TernaryBoehmRealsPrelude` ...

The files `BelowAndAbove` and `BelowLemmas` include ...

The file `upValue` ...

## Installation

...

## Future work

We have chosen to leave the dyadic rationals, and many lemmas
related to them, unformalised. We also do not directly define
any operations on the dedekind real numbers; instead, we
assume their existence and the existence of the expected
properties (for example, commutativity of addition). This is
because this work would be time consuming and is not a
contribution of our paper. However, formalising this part of
the library would be an interesting Agda project in and of
itself, and so it is a long-term goal for our project to
fully formalise these lemmas.

The file `FunctionMachinery` only gives negation as a completed
...

The file `TernaryBoehmRealsSearch` is incomplete. The fact
that any function on ternary Boehm encodings with a
continuity oracle yields a uniform continuity oracle that
can be used to search that function (Lemma ? in the paper)
has been assumed. This is because we prioritised formalising
other results over this extensive, but clearly true, lemma.
The formalistaion of this lemma is a priority for future work,
though may be very involved and require a lot of work.