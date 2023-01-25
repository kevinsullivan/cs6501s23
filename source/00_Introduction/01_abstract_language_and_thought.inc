
*******************
To Think Abstractly
*******************

To think abstractly, and certainly to perform scientific
reasoning effectively, we need languages in which we can
describe and reason about complex worlds. By a world we 
mean a collection of various objects of interest, having 
various properties of interest, and related to each other
in ways of interest. Formal mathematical logics provide 
us with such languages. 

Industrial programming languages are among such logics.
Logics of this kind have the property of being imperative: 
they are used to specify *procedures* that update memories 
and interact with worlds outside the logic (e.g., through
input/output (I/O) actions).

While the realm of practical programming languages--their
theory, design, implementation, and evolution--is vitally
important and deeply fascinating, it will not be the main 
topic or aim of this course.

We will use the foundational theoretical framework used
in much research in programming languages, namely type
theory; but where it's used in the programming languages
community to specify programming languages and to define
methods for reasoning about programs in such languages,
our aim is to understand how it's used as a foundation 
for the formalization of abstract mathematics.

The point of view driving this course is that in enough
domains to matter greatly, abstract mathematics is the
language of the field; and these are fields that we will
often want to program!

The idea of raising the abstraction level of programming
languages and programs is ages old. But these increases
in abstration are usually incremental and ad hoc, driven
by what can be computed efficiently at program compile or
run time.

Examples about. Dahl and Nygaard developed the concept
of objects (Simula 67). Simonyi introduced intentional
programming. Kiczales exhoted us to make the code look
like the design.

Our idea is different. we start with the observation
that Domains have already developed the
appropriate, often highly expressive, languages in which
to specify their worlds -- states of affairs amongst given
objects and relations that they care about. For example,
the algebra of affine spaces is very well suited for the
description of key elements in basic classical robotics,
while descriptions of fundamental particles of physics 
relies on the mathematics of tensor fields on topological
manifolds. 

- formal languages
- objects and their properties
- imperative vs declarative languages
- implementation vs specification
- programming vs abstract mathematics
- expressiveness vs tractability
