data Nat = Zero | Succ Nat
           deriving (Eq, Ord, Show, Read)

data Variable = U | V | W | X | Y | Z
                deriving (Eq, Ord, Show, Read)

data Expr = Val Nat
          | Var Variable
          | Mult Expr Expr
          | Div Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          deriving (Eq, Ord, Show, Read)

data Op = EVALMULT Expr
        | EVALDIV Expr
        | EVALADD Expr
        | EVALSUB Expr
        | MULT Nat
        | DIV Nat
        | ADD Nat
        | SUB Nat



type Cont = [Op] -- control stacks

type Store = [(Variable,Expr)] -- lookup table associates variables to nats

type Stores = [Store]
------------------------------- Store -----------------------------------

store :: Store
store = [(U, Val (Succ Zero)),
         (V, Val (Zero)),
         (W, Val (Succ (Succ (Succ Zero)))),
         (X, Val (Succ (Succ Zero))),
         (Y, Val (Succ Zero)),
         (Z, Val (Zero))]

store2 = [(U, Val (Succ Zero)),
         (V, Val (Succ (Succ (Succ Zero)))),
         (W, Val (Succ Zero)),
         (X, Val (Succ (Succ Zero))),
         (Y, Val (Zero)),
         (Z, Val (Succ Zero))]

stores :: Stores
stores = [store,store2]

find :: Variable -> Store -> Expr
find v s = head [n | (v',n) <- s, v == v']


delete :: Variable -> Store -> Store
delete v s  = [(v',n') | (v',n') <- s, v' /= v]


update :: Variable -> Store -> Expr -> Store
update _ [] n = []
update v (x:xs) n
  | (fst x) == v = (v,n):xs
  | otherwise = x:update v xs n

------------------------------- Arithmetic ------------------------------
-- Abstract Machine
eval :: Expr -> Store -> Cont -> Nat
eval (Val n) s c = exec c s n
eval (Mult x y) s c = eval x s (EVALMULT y : c)
eval (Div x y) s c = eval x s (EVALDIV y : c)
eval (Add x y) s c = eval x s (EVALADD y : c)
eval (Sub x y) s c = eval x s (EVALSUB y : c)
eval (Var v) s c = eval (find v s) s c

exec :: Cont -> Store -> Nat -> Nat
exec [] _ n = n
exec (EVALMULT y : c) s n = eval y s (MULT n : c)
exec (EVALDIV y : c) s n = eval y s (DIV n : c)
exec (EVALADD y : c) s n = eval y s (ADD n : c)
exec (EVALSUB y : c) s n = eval y s (SUB n : c)
exec (MULT n : c) s m = exec c s (mul n m)
exec (DIV n : c) s m = exec c s (n_div n m Zero)
exec (ADD n : c) s m = exec c s (add n m)
exec (SUB n : c) s m = exec c s (sub n m)


add :: Nat -> Nat -> Nat
add Zero n = n
add (Succ m) n = Succ (add m n)

mul :: Nat -> Nat -> Nat
mul Zero n = Zero
mul (Succ m) n = add (mul n m) n

sub :: Nat -> Nat -> Nat
sub n Zero = n
sub Zero (Succ Zero) = Zero
sub (Succ n) (Succ m) = sub n m

n_div :: Nat -> Nat -> Nat -> Nat
n_div _ Zero _ = Zero
n_div n f c
  | (d_sub n f c == Zero) = add (c) (Succ Zero)
  | otherwise = n_div n' f (add (c) (Succ Zero))
    where n' = d_sub n f c

d_sub :: Nat -> Nat -> Nat -> Nat
d_sub Zero _ _ = Zero
d_sub n Zero _ = n
d_sub (Succ n) (Succ m) c = d_sub n m c
-- d_sub Zero (Succ Zero) c = Zero


-- PROBLEM: Rounds up decimals when it shouldnt.

value :: Expr -> Store -> Nat
value e s = eval e s []

nat2int :: Nat -> Int
nat2int Zero = 0
nat2int (Succ n) = 1 + nat2int n

int2nat :: Int -> Nat
int2nat 0 = Zero
int2nat n = Succ (int2nat (n-1))

------------------------------- Equalities ------------------------------
data Statement = Less Expr Expr
               | LessEqual Expr Expr
               | Equal Expr Expr
               | More Expr Expr
               | MoreEqual Expr Expr
               | F
               | T

type Statements = [Statement]

evalStatement :: Statement -> Store -> Bool
evalStatement (Less w z) s = (value w s) < (value z s)
evalStatement (LessEqual w z) s = (value w s) < (value z s) || (value w s) == (value z s)
evalStatement (Equal w z) s = (value w s) == (value z s)
evalStatement (More w z) s = (value w s) > (value z s)
evalStatement (MoreEqual w z) s = (value w s) > (value z s) || (value w s) == (value z s)
evalStatement F _ = False
evalStatement T _ = True

evalPost :: Statements -> Store -> Bool
evalPost [] s = True
evalPost (x:xs) s
  |evalStatement x s = evalPost xs s
  |otherwise = False


------------------------------- Language ------------------------------
-- data a *->* b = Left a | Right b

data Lang = Assign Variable Expr
          | If Statement Lang Lang
          | While Statement Lang
          | Seq Lang Lang

inter :: Lang -> Store -> Store
inter (Assign v e) s = update v s (Val (value e s))
inter (If x l1 l2) s
  | evalStatement x s = inter l1 s
  | otherwise = inter l2 s
inter (While x l) s
  | evalStatement x s = inter (While x l) s'
  | otherwise = s
    where s' = inter l s
inter (Seq l1 l2) s = inter l1 s'
  where s' = inter l2 s

------------------------------- Triple --------------------------------

-- triple :: Statement -> Statement -> Store -> Lang -> Bool
-- triple p q s l
--   | evalStatement p s = evalStatement q s'
--   | otherwise = False
--     where s' = inter l s
--
triple :: Statements -> Statements -> Store -> Lang -> Bool
triple [] q s l = evalPost q s'
  where s' = inter l s
triple p@(x:xs) q s l
  |evalStatement x s = triple xs q s l
  |otherwise = False

triple_recursion :: Statements -> Statements -> Stores -> Lang -> Bool
triple_recursion p q [] l = True
triple_recursion p q (x:xs) l
  | triple p q x l = triple_recursion p q xs l
  | otherwise = False

pre :: Statement
pre = More (Var X) (Val Zero)

-- post :: Statement
-- post = Equal (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))

post :: Statement
post = Equal (Var X) (Var V)

post2 :: Statement
post2 = Equal (Var Y) (Var Z)

eg_assign :: Lang
eg_assign = Assign (X) (Val (Succ Zero))

eg_while :: Lang
eg_while = While (Less (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))) (Assign (X) (Add (Var X) (Val (Succ Zero))))

eg_seq :: Lang
eg_seq = Seq (Assign (Z) (Add (Var Z) (Var V))) (Seq (Assign (Z) (Add (Var Y) (Var Z))) (Assign (V) (Add (Var V) (Var Y))))

eg_if :: Lang
eg_if = If (Equal (Var X) (Val (Succ(Zero)))) (Assign (X) (Val (Zero))) (If (Less (Var U) (Var V)) (Assign (V) (Val (Succ Zero))) (Assign (V) (Val (Succ(Succ Zero) ))))

swap_vars :: Lang
swap_vars = Seq (Assign (Y) (Var Z)) (Seq (Assign (X) (Var Y)) (Seq (Assign (V) (Var Y)) (Assign (Z) (Var X))))
