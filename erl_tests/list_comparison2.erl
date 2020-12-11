main() -> [1,2,3] < [2,2] andalso
          [] == [] andalso
          [] < [1] andalso
          (not ([1] < [])) andalso
          (not ([1,2,3] < [1,1])) andalso
          (not ([1,2,3,4] < [1,2,3,4])) andalso
          [4,5] < [4,6].
