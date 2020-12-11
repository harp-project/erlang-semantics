main() ->
  element(1,{1,2,3}) == 1 andalso
  element(1+1,{foo,bar,3}) == bar andalso
  element(3,{1,2,3}) == 3. 
