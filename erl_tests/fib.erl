fib(0) -> 0;
fib(1) -> 1;
fib(N) -> fib(N - 1) + fib(N - 2).

fib2(N) -> f(N,0,1).
f(0,A,B) -> A.
f(N,A,B) -> f(N- 1, B, A+B).

	    
main() -> fib(9) == fib2(9).


