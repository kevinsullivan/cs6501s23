


def factorial : ℕ → ℕ           -- remember, no := here
| 0 := 1
| (n' + 1) := (n' + 1) * factorial n'


/-  TEXT:
You might be tempted to use (n-1) as the argument to the
recursive call. That won't work. The problem is that this
is a function application expression (whereas nat.succ n
is a very particular kind of application), and Lean can't
tell whether it'll always be "smaller than n". If it were
not, the recursion could go "open loop" and not terminate.
def factorial2 : ℕ → ℕ           -- remember, no := here
| 0 := 1
| n := n * factorial2 (n-1)     -- can't prove termination


#eval factorial 5


