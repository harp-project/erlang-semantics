main() ->
  is_atom(apple) andalso
  not (is_atom(12)) andalso
  is_integer(5+6) andalso
  not (is_integer({1,2,3})) andalso
  is_number(12) andalso
  not (is_number(apple)) andalso
  is_boolean(2 < 3) andalso
  is_boolean(false) andalso
  not (is_boolean(apple)) andalso
  not (is_boolean(1)).
