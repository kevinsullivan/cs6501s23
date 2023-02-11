
Elementary Discrete Mathematics DevOps
======================================

This is the development environment for [CS6501 Spring 2023](https://www.computingfoundations/).

The `lean_source` directory contains all of the information needed to produce one 
volume of Elementary Discrete Mathematics. Each major topic is published as a volume:
Valid reasoning. Propositional logic. A predicate logic. Sets theory. Combinatorics.
Probability. Number Theory.

- Edit `.lean` with Avigad-style markup files in `lean_source` 
- From root directory, `lean_source/mkall.sh` generates `.rst` files 
  - in `source.` for the book
  - an exercise file and a solution file for each section 

Have [Sphinx and ReadTheDocs](https://sphinx-rtd-tutorial.readthedocs.io/en/latest/install.html).

The following files are maintained by hand:
- The file `source/index.rst` should have an entry for each chapter.
- For each chapter, there should be a `.rst` file in `source`. It should include
  each of the sections.
- For each section, there should be a `.lean` file in the appropriate place
  in `lean_source`.
- Each section should have a corresponding line in `lean_source/mk_all.sh`.

Numbering in outputs is determined by sphinx labels

- \# with overline, for parts
- \* with overline, for chapters (individual lean file)
- \=, for sections
- \-, for subsections
- \^, for subsubsections
- \“, for paragraphs


- lean_source/mkall.sh
- make html
- make latexpdf
- deploy.sh (fix)
  
The script `deploy.sh` KS: FIX deploy everythings (textbook 
and user version of the example and solution files) to an 
arbitrary repository, set up to use the `gh-pages` branch
to display the html. Specifically, we use the following:
./deploy.sh leanprover-community mathematics_in_lean

TODO: pygmentize -S default -f html > style.css; replace "default" w/ style