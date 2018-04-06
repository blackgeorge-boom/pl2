
main = do
  all <- getContents
  let (sn : sl : sb : rest) = words all
  let n = read sn
  let l = read sl
  let b = read sb
  let x = map read rest
  -- Τα type annotations μάλλον δε θα χρειάζονται στη δική σας λύση...
  print (n)
  print (l)
  print (b)
  print (x)
