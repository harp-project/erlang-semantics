main() ->
  case 3 of
    3 when 1 < 2; 1 > 2 -> ok;
    3 when 1 < 2; 2 < 3 -> nok
  end == ok.

