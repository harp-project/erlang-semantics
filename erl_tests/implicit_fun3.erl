f(X,Y,Z) -> X + Y + Z.

main() -> 
  begin
    F = f,
    A = 1 * 2 + 1,
    Fun = fun F/A,
    Fun(1,2,3)
  end == 6 .
