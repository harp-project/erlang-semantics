main() -> 
  12 < alma andalso
  12 < {1,2} andalso
  12 < [1,2] andalso
  alma < {1,2} andalso
  alma < [1,2] andalso
  {1,2} < [1,2] andalso
  not (alma < 12) andalso
  not ({1,2} < 12) andalso
  not ([1,2] < 12) andalso
  not ({1,2} < alma) andalso
  not ([1,2] < alma) andalso
  not ([1,2] < {1,2}).
    
