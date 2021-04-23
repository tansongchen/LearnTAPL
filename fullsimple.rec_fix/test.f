/* Examples for testing */

ff = lambda f:Nat->Nat->Nat.
  lambda x:Nat.
    lambda y:Nat.
      if iszero x then y else (f (pred x)) (succ y);

plus = fix ff;

plus 10 105;
plus 0 1;
plus 0 0;
plus 2 0;
