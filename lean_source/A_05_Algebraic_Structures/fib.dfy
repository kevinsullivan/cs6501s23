// pure functional (mathematical) *specification* of n'th Fibonacci number
function fib(n: nat): nat
    ensures fib(n) == (n == 0 ? 0 : (n == 1 ? 1 : fib(n-1) + fib(n-2)))
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    } else {
        return fib(n-1) + fib(n-2);
    }
}

// efficient imperative *implementation* of computation of n'th Fibonacci number
method Fibonacci(n: nat) returns (result: nat)
    ensures result == fib(n)    -- implementatin must satisfy specification
{
    var a := 0;
    var b := 1;
    result := 0;

    if n == 0 {
        result := a;
    } else {
        for i: nat := 1 to n {
            result := a + b;
            a := b;
            b := result;
        }
    }
}