/* Examples for testing */

r = ref(lambda n:Nat. lambda m:Nat. n);
f = lambda n:Nat. lambda m:Nat. if iszero n then m else (!r) (pred n) (succ m);
r := f;
plus = !r;

plus 10 105;
plus 0 1;
plus 0 0;
plus 2 0;
