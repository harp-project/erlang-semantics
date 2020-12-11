gcd(A, 0) -> A;
gcd(A, B) -> gcd(B, A rem B).


main() -> gcd(42, 60) == 6.


