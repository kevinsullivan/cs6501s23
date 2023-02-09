
*******************
To Think Abstractly
*******************

To advance science and engineering, we need languages in
which we can describe and reason about complex worlds. By 
a *world* we mean a collection of objects of interest and
their structures, properties, behaviors, relations to each 
other. 

Abstract Mathematics
--------------------

Mathematics and formal logics provide such languages. They 
give us the intellectual tools we need to think abstractly 
and yet with great precision about rich and complex systems: 
to represent, reason about, and ultimately design complex 
worlds that would otherwise remain beyond our grasps.   

As an example, the abstract mathematics of linear and affine
spaces give us languages for describing, reasoning about, and
designing systems that work in the *classical* physical world
we experience every day. The abstract mathematics of tensor
fields on topological manifolds are essential for describing,
reasoning about, and designing interventions in the *quantum* 
world of particle physics.

By the term, *abstract*, we mean that descriptions in such
languages represent relevant phenomena precisely, concisely, 
and without any unnecessary complexity or inessential detail. 

As an example, a physicist might represent two accelerations
applied to a drone in a three-dimensional geometric space in
abstract, coordinate-free terms, by writing this: *let a₁ and 
a₂ be accelerations of the drone.* This formulation is abstract
insofar as no coordinates are given for these vectors. The 
assignment of coordinates to *physical* quantities is usually
arbitrary and unnecessary to express. A physicist might, for 
example, represent *the sum of these accelerations* simply as
*a₁ + a₂.* This expression has an absolutely precise physical 
meaning even though it's abstract. 

A programmer, by contrast, would typically jump to a choice
of some coordinate system and would then represent the two
physical quantities in the concrete (*parametric*) terms of
tuples of floating point numbers; with the summation of the
physical accelerations represented by element-wise floating
point addition of the corresponding coordinate tuples. 

Costs of Concreteness
---------------------

This ubiquitous approach to programming physical computations
is problematical in multiple dimensions. First, as mentioned,
it substitues concrete representations for abstract, adding
inessesntial complexity to models and computations. Second,
it generally strips away crucial mathematical properties of
the abstract representations of objects of interest, making
it impossible to check programs for consistency with such
mathematics.

For example, in the *tf* and *tf2* affine space libraries of
the Robot Operating System (ROS) platform for the programming
of terrestrial robots, points and vectors are represented in
the concrete terms of coordinate tuples relative to arbitrary 
coordinate frames. But it gets worse: points and vectors in
this framework are aliases for the same concrete type: a type
of floating-point tuples. 

This means, among other things, that one can add points to 
points in *tf* without receiving any type errors from the 
programming language system, even though addition of points 
to points makes no physical sense and is inconsistent with
the abstract mathematics of the domain. In an affine space,
there is no operation for adding points to point. 

The nearly exclusive use of concrete representations in most
everyday programming complicates software design and reasoning
by requiring the manipulation of often complex, inessential 
details. And because so much of the structure of the mathematics 
of the domain is *forgotten* in the programming code, it also
becomes impossible for the programming system to check for what 
we might call *full physical type consistency*. 

Programming code thus generally ends up deeply disconnected
from the abstract mathematics of the physics of the domain that 
it's meant to represent, manipulate, implement, and free to
carry out inconsistent operations. As one example, programmers
often struggle mightily using different frames of reference in
a consistent manner, e.g., by adding vectors represented by
numerical tuples but with coordinates expressed in different 
frames of reference. 

A special case, by the way, is operating incorrectly on values 
because they are expressed in different units, such a meters 
and feet. We can understand 1 meter and 1 foot as each being
a basis vector for the *same* one-dimensional physical space.
Clearly adding numerical values of 2 (feet) and 3 (meters) to 
produce 5 of *something,* produces a meaningless result. 

A Path Forward
--------------

So why haven't we already deeply connected concrete to code
the abstract mathematics of the domain in which it's meant 
to operate? Perhaps the most fundamental reason is that math
has up until recently been a quasi-formal, paper-and-pencil
exercise, making it, hard even impossible, to connect code
to such mathematics. 

Now, with rapidly developing work by a still small set of
ressearchers in mathematics, the complete formalization and
mechanization of advanced abstract mathematics is becoming
a reality. As and example Massot and his colleagues in 2022
managed to formalize not only a statement, but a proof, of 
the local h-principle for first-order, open, ample partial 
differential relations, with the possibility of eversion of
the 3-sphere as a corollary. 

Their work showed that their approach to formalizing 
mathematics is no longer useful mostly just for abstract 
algebra, but that it also now promises advances in abstract 
geometry (e.g., on manifolds), which is at the very heart
of not only terrestrial robotics but also modern physics
and perhaps even areas such areas as deep learning.

The Vision
----------

The insight driving this class is that this kind of work 
from the  mathematics community is now making it possible 
to develop *computable abstract mathematics* for purposes
of software engineering. Promising application domains for
such work clearly include divere cyber-physical systems and
might be relevant to deep learning as well, with its basic
assumption that real-world data have geometric properties, 
such as lying on high-dimensional manifolds. 

What we seek are ways to enable use of the abstract mathematical 
languages of such domains, coupled with concrete representations
to support computation, with *full physical type checking* of the 
physical mathematics; *foundational proofs* of correctness of the
mathematics; and explicit link to concrete (often coordinate-based) 
representations that are necessary in practical implementations.

This Class
----------

The purpose of this class is to introduce computer science
students to the ideas necessary to pursue both research and
development activities based on these ideas. We will use the
preferred tool of the community of mathematicians pushing the
formalization of mathematics, namely the Lean Proof Assistant,
developed by Leo DeMoura at Microsoft research, and the ever
growing *mathlib* library of formalized mathematics.
