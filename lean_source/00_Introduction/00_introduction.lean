/- TEXT:

CS6501: Special Topics in Software Engineering, Spr23.
======================================================

This is a special topics course in software engineering. The idea 
that we will explore is that we can now import ongoing advances 
in the formalization of abstract mathematics (in type theory and
to a significant extent around the Lean prover and its mathematics
libraries) as new foundations for engineering software programs for
systems that inhabit domains that have such abstract mathematical 
underpinnings. Such domains include physics, and thus also a broad
range of cyber-physical systems.

Along the way, you'll learn formal logic and proof construction, 
foundations of programming languages, functional programming, and 
more. By the end you will know how to use some cutting-edge tools, 
type theory and constructive logic proof assistants, to formalize 
the abstract mathematics of important application domains. 

What does *abstract* mean here?
-------------------------------

Here, the adjective, abstract, means *being coordinate-free*. 
For the opposite of *abstract*, we'll use *parametric*. The idea 
is that a mathematical object, such as a vector, can be understood
simply as such, with no reference to coordinates; or that same abstract
vector can be represented concretely/parametrically as a struture of
parameter values expressed relative to some given frame of reference.

Why *abstract* mathematics?
---------------------------

A premise of this class is that domain experts (e.g., in the
physics of terrestrial robotics, or of elemenary particles) speak,
model, analyze, and understand the operation of systems in the 
abstract mathematical language of the domain, and very often not
in terms of ultimately arbitrarily selected frames of reference . 

This is clear in physics where complex mathematical structures 
such as tensor fields on topological manifolds are essential for
precise definitions of phenomena in particle physics. 

Domain-specific abstract mathematics formalized in type theory 
is what we see as an important language of the domain, to serve 
as a basis for programming with static checking of abstractions,
and with parametric representations carried along as necessary.

What is the point?
------------------

A remarkable feature of constructive logics as hosted by many
proof assistants is that they can compute. Computation is now
wholly integral to practical logical reasoning if only because
some proofs require systematic case analysis over very large
numbers of cases, given as the outputs of other computations.

This is is relevant because it suggests that fully formalizing
the fully developed mathematical language of the given domain,
we will be well on our way to having reference specifications 
and with computable implementations. 

Going even further, the most recent version of Lean is intended
as an efficient general-purpose programming language as well as 
a proof assistant, compiling to C, and with workable language 
interoperability interfaces.

In the future we expect to be able to statically type check and 
foundationally verify "code" written in the abstract mathematics
of the domain and with very little custom coding needed also to
have corresponding verified implementations, even if only used as
test oracles for production code.  

This is the of abstract specifictions from which concrete 
implementations are derived. I will not say refined because 
in practice most derivations are not refinements but rather
toyish models of semantically rich and complex computations
in the source domain.

This class
----------

The first major part of this class will teach you the fundamentals
of programming and reasoning in Lean 3. We will mainly use Lean 3, 
nothwithstaning that Lean 4 is garnering real attention and effort.
Student might wish to explore Lean 4 as an optional class activity.

The second part of the class will focus on how to formalized abstract
mathematical structures in Lean, and how we might such capabilities 
to  these advances in formalizing mathematics to help meet 
the need for statically type checked specifications in the abstract
language of the domain, with corresponding parametric representations
carried along for computational possibly and oher purposes. 

TEXT. -/