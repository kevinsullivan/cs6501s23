
Mathematical Foundations of Physical Computations
=================================================

TL;DR
-----

This repo supports the development and delivery of a
set of course notes for a coures at the University of 
Virginia, on how we might leverage advances in the
formalization of abstract mathematics to fundamentally
improve software engineering. The deployed notes as of
now are [here](https://www.computingfoundations.org).

Motivation
----------

For millenia, to the present day, abstract mathematics
has been an analog, paper-and-pencil, pursuit.  For most
of that time, there was nothing but paper and pencil, of
course and that's what it mostly remains.
 
 
One downside of this state of affairs is that it keeps
it hard to formally relate software (purely digital) to
the abstract mathematics of the domain, that it's meant 
to implement, expressed in the concrete languages of
practitioners in these domains (e.g., physics, Einstein
notation for tensors, coordinate-free points on smooth
manifolds, and charts imposing coordinate systems on them,
that the software is meant to implement.

This work has been funded in part by the National Science Foundation as part of our project on the Physical Semantics
of Code. In this project we are devising, realizing, and 
evaluating new concepts and methods for constructing software
in statically typechecked and foundationally verified abstract
mathematics--the mathematics of any given domain. For now we
are working on classical physics in the service of robotics 
and cyber-physical systems more generally.

This is vague. Feel free to reach out: sullivan@virginia.edu.

This Repository
---------------

This repository is the course development and delivery platform for CS6501, Special Topics in Software Engineering, Abstract Mathemtical Foundations, being taught in the Spring of 2023.

The rest of this document is entirely for my own use. It presents instructions, mostly for myself, on how to use it.

Some elements of the (not yet fully automated or very flexible) Sphinx-based workflow implemented here was adopted, with many thanks for making it available, from Jeremy Avigad's public site in support of a different project and presentation.

Technical Nonsense
------------------

The `lean_source` directory contains all of the information needed to produce notes for one course. Each major section of
a course is a set of chapters, A section is represented by a
folder. A chapter by a file within that folder. Within a chapter,
subdivisions are by use of _______ section notations. 

Follow the naming conventions. When you add file/chapters or 
folders, it's necessary to manually update the *mkall.sh* script 
file.

Beyond a brief introductory chapter, at the time this is being
written, there is just one other section, on propositional logic
and a verified, nicely designed implementation of this language.

- Edit `.lean` files using Avigad-style markup in `lean_source`
- From homedir, `lean_source/mkall.sh` generates `.rst` files 
  - in `source.` for the book
  - an exercise file and a solution file for each section in ___

Dependencies
------------
This repo uses VSCode remote containers and a customer docker
image. All essential dependencies should be installed and you
should be nearly ready to start producing content. The require
pre-step is to create an aws credentials file in /root/.aws with
the aws credentials for the aws user on whose behalf operations
will run on the AWS back end. (You need to have in place VSCode with its Remote Containers extension, and Docker Desktop.)

Manual Processes
----------------

The following files are maintained by hand:
- The file `source/index.rst` should have an entry for each chapter/dicrectory.
- For each chapter/directory, there should be a `.rst` file in `source`. It should include
  - each of the sections.
  - For each section, there should be a `.lean` file in the appropriate place in `lean_source`.
- Each section must have a line in `lean_source/mk_all.sh`.

Header Style
------------

Numbering in outputs is determined by sphinx labels

- \# with overline, for parts
- \* with overline, for chapters (individual lean file)
- \=, for sections
- \-, for subsections
- \^, for subsubsections
- \“, for paragraphs

Build Script
------------

From the top-level directory of the cloned repo do this:

- lean_source/mkall.sh
- make html
- make latexpdf
- deploy.sh (TODO: needs to be fixed)
- instead follow instructions in UPLOAD.md
  
The script `deploy.sh` KS: FIX deploy everythings (textbook
and user version of the example and solution files) to an
arbitrary repository, set up to use the `gh-pages` branch
to display the html. Note: Avigad uses the following here:
./deploy.sh leanprover-community mathematics_in_lean

Implementation
--------------

The lean markup processing program is in the lean_sphinx.py
file.

