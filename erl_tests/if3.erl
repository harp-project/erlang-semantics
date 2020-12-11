talk(Animal) ->
  Talk =
    if
      Animal == cat  -> meow;
      Animal == beef -> mooo;
      Animal == dog  -> bark;
      Animal == tree -> bark;
      true -> fgdadfgna
    end.

main() -> talk(beef) == mooo.
