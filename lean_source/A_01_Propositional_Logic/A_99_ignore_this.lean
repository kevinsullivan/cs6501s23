/-
A semantics starts with a definition of what all
of the the relevant individual variables mean. In a language
of arithmetic we will take them to mean integers values (from
algebra itself). 

Now, given such a mapping from variables (here ** and *y*) to
semantic meanings (here the values 3 and 8), we can define the
meanings of all expressions that can be constructed by putting
*+* between any two smaller expressions. 

Consider the expression, *x + y*, under an interpretation, 
*i* = { x ↦ 3, y ↦ 8}. Now start with the main connective. 
Here it's *+*. Evaluating it reveals that it means the integer
addition function. We then recursively evaluate each of the 
smaller expressions (*x* and *y*) that it combines. To find
the meaning of any variable expression, such as *x*, we just 
apply the given interpretation to the variable. We will write
this as *i x*. In Python or C it would be i(x). It returns
the specified meaning of the given variable under the given
interpretation, *i*.  Clearly (i x) = 3 and (i y) = 8. To
compute the final meaning of *x + y* when apply the meaning
of *+* (integer addition) to the meanings of *x* and of *y* 
(3 and 8, respectively) to obtain the meaning of *x + y*. Of
course it's *11*.

  are arithmetic 
variable expressions, let's say with semantic meanings of 3
and 8 respectively, then *x + y* is also an expression,
constructed by the rule that allows the addition syntax
operator to be applied to any two arithmetic expressions to
construct a new larger one.


to be  and given the specified meanings of *x*
and *y*, its meaning is 11. 

The set of strings of a language can sometimes be specified 
compactly by a *grammar*: a finite set of rules that generate
(construct) all of the strings of the language.

As we'll see shortly, one elegant way to specify certain
grammars is as an inductive data type, the constructors of
which generate all and only the well formed formulae strings of  in the language.


The strings are called the *well formed formulae* (or *wffs, 
terms, or expressions*) of the language. The semantics of a
formal language is as assignment of meanings to expressions.

It is possible, in general, that only some expressions in a
a given language have meanings as defined by the semantics 
of the language. For example, if we understand the meaning 
of a computer program (a string) to be the value that it 
outputs when it terminates, then some programs won't mean
anything at all: namely those that go into infinite loops
and thus never terminate.

Making things simpler, every expression in propositional
logic has a meaning in the form of a Boolean (true/false)
value, provided that one is given a Boolean meaning for 
each of the variables that can appear in the variable
expressions in the language.
-/
