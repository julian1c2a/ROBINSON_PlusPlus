open Char in
example (c d : Char) (h : c.toNat = d.toNat) : c = d := by
  apply Char.ext
  apply UInt32.ext
  omega
