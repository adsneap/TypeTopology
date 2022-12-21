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

The formalisation library is built in Martin Escardo's Agda
library `TypeTopology`, which formalises a huge portion of
mathematics in constructive, univalent type theory. Its approach
is compatible with that of the HoTT book.

## Installation

Each main file in this library is a literate Agda file that
provides commentary on the definitions and proofs being
formalised. Therefore, we simply recommend that one views the
files in the GitHub browser, which provides a nice interface
for both the code and markdown.

If one prefers, then one should download Escardo's `TypeTopology`
library at commit ???, and place the files of this repo in a
new folder `source/PLDI/`. The files can then be compiled using
Agda; the instructions of installing which can be found online.

## Overview and relationship to paper

Our paper's supplementary Java and Agda code were written in
parallel and, thus, they are very alike. For example, the
machinery to lift functions is virtually the same in both
languages -- it simply has to be formalised in Agda, rather than
"assumed to work" as in Java. This alikeness is intended, as we
wish the Agda library to be seen as a formalisation of the Java
API.

### Main files

[`TernaryBoehmReals`](1-TernaryBoehmReals.lagda.md) defines the
type of ternary Boehm reals that the paper/API uses for searching
real numbers. Chiefly, we define encodings of reals in compact
intervals and prove a rather tedious lemma that shows we can
build an encoding that goes directly through two given
specific-width encodings of compact intervals.

[`FunctionEncodings`](2-FunctionEncodings.lagda.md) then defines
types for sequences on variable-width and specific-width interval
encodings as in the paper's Sections 3 and 6. We show that these
sequence encodings can be used to define encode real numbers,
and show how the ternary Boehm reals also arise from the same
principles. Importantly, we provide machinery that allows the
lifting of approximated functions on the mathematical real space
to functions on ternary Boehm reals. We provide negation as an
example, though the Java API has more examples.

[`TernaryBoehmRealsSearch`](3-TernaryBoehmRealsSearch.lagda.md)
combines the two files above to formalise how ternary Boehm
encodings can be used to search encodings of functions on the
mathematical real space. It gives the definition of a searchable
type and shows that uniform predicates on compact intervals of
ternary Boehm encodings are searchable. Then, it shows the idea
of how functions encoded using the aforementioned machinery can
be used to provide searchable predicates based on the codomain 
of these functions.

### Supplementary files

[`Prelude`](Prelude.lagda.md) includes a variety of definitions
and lemmas that are needed for our work but are not in
`TypeTopology'. This includes extra lemmas on the integer
ordering and on vectors.

[`DyadicRationals`](DyadicRationals.lagda.md) defines the type of
dyadic rational numbers -- i.e. those rationals of form `k/2^i`
where `k, i : ℤ`.

[`DyadicReals`](DyadicReals.lagda.md) defines the type of
Dedekind real numbers using dyadic rational numbers. This is used
as our type of 'mathematical' real numbers throughout the
library.

[`BelowAndAbove`](BelowAndAbove.lagda.md) consists of a bunch of
lemmas needed for the structural operations on the ternary Boehm
encodings.

[`upValue`](upValue.lagda.md) defined the operation `upValue`,
which is based on `log₂` and used in our function machinery.

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

`FunctionMachinery` only gives negation as a completed example.
In the future, we will provide projection, addition,
multiplication and composition as further examples.

`TernaryBoehmRealsSearch` is incomplete. The fact that any
function on ternary Boehm encodings with a continuity oracle
yields a uniform continuity oracle that can be used to search
that function (Lemma 6.28 in the paper) has been assumed. This
is because we prioritised formalising other results over this
extensive, but clearly true, lemma. The formalistaion of this
lemma is a priority for future work.