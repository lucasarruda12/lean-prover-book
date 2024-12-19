namespace ArEx

inductive ArExV where
  | const : Nat -> ArExV
  | var   : Nat -> ArExV
  | plus  : ArExV -> ArExV -> ArExV
  | times : ArExV -> ArExV -> ArExV

open ArExV

def assign (v : Nat) (n : Nat) : ArExV -> ArExV
  | var v' => if v == v' then const n else var v' 
  | plus t s => plus (assign v n t) (assign v n s)
  | times t s => times (assign v n t) (assign v n s)
  | const n => const n 

end ArEx
