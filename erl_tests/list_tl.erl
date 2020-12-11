main() ->
  tl([1,2*1,1+2]) == [2,3] andalso
  tl([0+1,2 | [3]]) == [2,3] andalso
  tl([1 | apple]) == apple.
