# Summary Notes for 8/30/22

## Distributed Version Control Using Git and GitHub

We covered how to use git and GitHub this semester to receive updates and new files from Prof. Sullivan. We won't test you on this material, but it's good to know, beingindustrially useful as well as interesting.

## Procedural vs. Declarative Expressions

Ordinary *code* languages support the definition of *procedures,* that, when executed, compute answers to particular problems. Code written in such a *procedural logic* (including Python, Java, etc.) defines *how* to compute a desired result.

By contrast, a *declarative specification* uses a more expressive logic to formally state what properties a desired solution must have to be acceptable.

Consider, for example, the function, f(x) = non_negative_sqrt(x), where x is a non-negative real number, and f(x) is the non-negative square root of x. When x=0 both square roots are zero, so it doesn't matter which you pick!

### Procedural Implementation

Here's an implementation of Newton's method for computing the square root of a non-negative number to within a small margin of error, by iteratively applying an update process to an initial "guess" until the error, in the form of the difference between the guess squared and the number whose square root is to be computed, is less than a small, pre-set error tolerance term (e.g., maybe .0001 or something). I acknowedge following site for posting this code: <https://www.geeksforgeeks.org/find-root-of-a-number-using-newtons-method/>

```python
# Python3 implementation of the approach

# Function to return the square root of
# a number using Newtons method
def squareRoot(n, l) :

	# Assuming the sqrt of n as n only
	x = n

	# To count the number of iterations
	count = 0

	while (1) :
		count += 1

		# Calculate more closed x
		root = 0.5 * (x + (n / x))

		# Check for closeness
		if (abs(root - x) < l) :
			break

		# Update root
		x = root

	return root

# Driver code
if __name__ == "__main__" :

	n = 327
	l = 0.00001

	print(squareRoot(n, l))

```

Just glancing at this code, one might not immediately conclude that its purpose is to compute square roots. Procedural code trades away expressiveness (transparency and understandability of meaning) for efficiency of evaluation on an electronic digital computer.

## Decarative Specification

By contrast, one can describe declaratively rather than procedurally  *what* the square root of any given non-negative number, *x*, is, and the result is dramatically clearer. The square root of a non-negative number, x, is defined as follows:

```en
sqrt x := y | y * y = x. 
```

Pronounce this as, "the square root of x is defined to be a value, y, whose square is x." You could read it even more straigtforwardly as " the square root of x is a value, y, *such that* y squared equals x").

## Comparison and Contrast

One one hand, the Python program runs fast and *computes* square roots. The program explains *how* in a clever way to compute a (close approximation of any) defines *how* to compute a square* root. What it does describe is a procedure. What it doesn't express very well at all is what a square root is.

Now, for a contrast, consider the specification. It's enormously better in the clarity and abstract precision with which it defines *what* a square is, but it doesn't even give us a good start on a procedure to compute sqrt(x) for any suitable argument, x.

## Abstract Logics are for Precise Human Expression of Complex Ideas

Propositional logic (PL), PL enriched with additional "theories" (as you've already seen) and other even more expressive logics are meant in large part to support *human-oriented* but still rigorously precise expression of potentially very complex ideas.

You can see that expressing the concept of the square root function in Python yields a mess of an expression. It's understandable, with effort, by someone who is skilled in the craft of everyday Python programming. But it's hardly the definition of square root you'd want to see in a math book, or learn first in high school.

What this class will give you are the superpowers that come from being able to express very complex ideas, both in any beyond the realm of computer science, through proficiency in the concepts of logical expression and reasoning.

## Examples

The rest of this class was a few examples plucked from here: <https://ericpony.github.io/z3py-tutorial/guide-examples.htm>. In each case we copied and pasted the code into new a Python (.py) file in the mywork directory, and that had a discussion about the example. 

The last example was the most fun. We went over the rules of Sudoku informally (in spoken English) then saw how to *formalize* the rules of the game in the logic of Z3 (combining propositional/Boolean logic and satisfiability, as well as a variety of mathematical and computer science data types). The examples we studied, copied into a Python file, ran, and then discussed, were as follows:

### Even just simplifying expressions is fun!

```python
x = Int('x')
y = Int('y')
print simplify(x + y + 2*x + 3)
print simplify(x < y + x + 2)
print simplify(And(x + 1 >= 3, x**2 + x**2 + y**2 + 2 >= 5))
```

### Simultaneous non-linear equations (oh wow)

```python
x = Real('x')
y = Real('y')
solve(x**2 + y**2 > 3, x**3 + y < 5)
```

### The Dog, Cat, and Mouse puzzle

Consider the following puzzle, as expressed informally in *natural language,* (English). The crucial challenge is to learn how to write constraints explained in English instead in mathematical logic. We covered this example to emphasize and exemplify this point.

```en
Spend exactly 100 dollars and buy exactly 100 animals. Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents each. You have to buy at least one of each. How many of each should you buy?
```

To get started, give names to the unknowns: to represent how many cats to buy, well use *cats*, and similarly for dogs and mice. Next express the constraints using mathematical logic notations rather than English.

- "You have to buy at least one cat" becomes "cats >= 1"
- You must buy a hundred animals becomes "cats + dogs + mice = 100"
- and now we must leave it to you to write the remaining ones (try before you look at the z3 specification)

Instead of writing *procedural* code that defines *how* to search for values of cats, dogs, and mice that satisfy all the constraints, now you just write the constraints *declaratively*, and leave it to the "solver" to solve the constraints. 

### Sudoko

Finally, we studied the declarative specification of Sudoko, which you will also find in the same document.

## What to do if you missed class

Read this material. Talk to the TAs or Sullivan if you need to. But most importantly, do the work that the students in class did, copying the specififations into actual Python files, studying them as examples of declarative specifications, and just marvel at how you can now solve problems using computers by expressing constraints on a solution and using a satisfiability solver rather than by writing what you should now see are pretty tangled expressions in procedural (also called imperative) programming languages. (You can see the code for Newton's method for square roots in several languages on the site I've linked. None is remotely as crystal clear and noise-free as our declarative specification.)