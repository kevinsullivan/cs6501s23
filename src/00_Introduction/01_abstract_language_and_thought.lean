
/-
The idea of raising the abstraction level of programming
languages and programs is ages old. But these increases
in abstration are usually incremental and ad hoc, moving
in small steps from the language of the machine closer to
but never really approaching the richness of the abstract
mathematics of the domain, using its concepts, notations,
prior results, and so forth. 

Industrial programming is driven by the idea that the 
essential content of a program is a set of concrete 
representations, usually with *lightweight abstractions*
that serve at least remind the programmer of the actual
and *intended* (but implicit and unchecked) mathematics 
being implemented. This paradigm can work of course, but
at the cost of loss of abstraction, addition of ancillary 
complexity, loss of static checking of the the abstract
mathematics, the absence of proofs of correctness of the
mathematics itself, and many consequences in terms of loss
of productivity, safety, reliability, and other critical
system properties. 

[Some related work. Examples abound. Dahl and Nygaard 
developed the concept of (software/runtime) objects to
represent corresponding physical phenomena (Simula 67). 
Simonyi introduced *intentional programming*. Kiczales 
exhoted us to make the code look like the design and to
this end extended work in *aspect-oriented programming*
to enable the lightweight abstraction of *crosscutting
(thus hard to modularize) concerns* in programs. 

But all
such attempts start from code and seek to incrementally
improve abstraction capabilities. We start with the fully
formalized, mechanized, and abstract mathematics of the 
domain as the most natural language in which to express
computations, and then move from there to *lightweight*
(semantically stripped down but efficiently executable)
code. 

Our idea is different. we start with the observation
that Domains have already developed the appropriate, often 
highly expressive, abstract mathematical languages in which
to specify their worlds. For example, the abstract algebra 
of affine spaces is well suited for the description of the 
temporal and geometric spaces in which classical robots 
operate. Descriptions of fundamental particles of physics 
relies on the mathematics of tensor fields on topological
manifolds.

Linking such abstract mathematics to code has always been
a manual processes. Now, however, with the automation of
abstract mathemtics by parts of the mathematics community
using constructive logic proof assistants and type theory,
that has become possible. This course will teach you the
basic concepts that you will need to start to make such
connections.
-/