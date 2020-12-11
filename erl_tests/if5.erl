f() -> ok.

main() ->
  if
    false              -> 1;
    false, true        -> 2;
    false, true; 1+2   -> 3;
    false; true; false -> 4;
    true               -> 5
  end == 4.
