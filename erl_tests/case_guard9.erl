main() ->
  case 3 of
    3 when true -> ok;
    3 when false -> nok 
  end == ok.

