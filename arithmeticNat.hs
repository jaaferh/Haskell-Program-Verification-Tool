data Nat = Zero | Succ Nat
           deriving (Eq, Ord, Show, Read)

data Variable = U | V | W | X | Y | Z
                deriving (Eq, Ord, Show, Read)

data Expr = Val Nat
          | Var Variable
          | Mult Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          deriving (Eq, Ord, Show, Read)

data Op = EVALMULT Expr
        | EVALADD Expr
        | EVALSUB Expr
        | MULT Nat
        | ADD Nat
        | SUB Nat


type Cont = [Op] -- control stacks

type Store = [(Variable,Expr)] -- lookup table associates variables to nats

------------------------------- Store -----------------------------------

store :: Store
store = [(U, Val (Succ Zero)),
         (V, Val (Zero)),
         (W, Val (Succ (Succ (Succ Zero)))),
         (X, Val (Succ (Succ Zero))),
         (Y, Val (Succ Zero)),
         (Z, Val (Zero))]

store2 = [(U, Val (Zero)),
          (V, Val (Zero)),
          (W, Val (Zero)),
          (X, Val (Succ Zero)),
          (Y, Val (Zero)),
          (Z, Val (Zero))]

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
eval (Add x y) s c = eval x s (EVALADD y : c)
eval (Sub x y) s c = eval x s (EVALSUB y : c)
eval (Var v) s c = eval (find v s) s c

exec :: Cont -> Store -> Nat -> Nat
exec [] _ n = n
exec (EVALMULT y : c) s n = eval y s (MULT n : c)
exec (EVALADD y : c) s n = eval y s (ADD n : c)
exec (EVALSUB y : c) s n = eval y s (SUB n : c)
exec (MULT n : c) s m = exec c s (mul n m)
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


value :: Expr -> Store -> Nat
value e s = eval e s []


-- validationAdd :: Expr -> Expr -> Expr -> Bool
-- validationAdd a b e
--   | add (value a s) (value b s) == value e = True
--   | otherwise = False
--
-- validationMult :: Expr -> Expr -> Expr -> Bool
-- validationMult a b e
--   | mul (value a) (value b) == value e = True
--   | otherwise = False
--
-- validationSub :: Expr -> Expr -> Expr -> Bool
-- validationSub a b e
--   | sub (value a) (value b) == value e = True
--   | otherwise = False



------------------------------- Equalities ------------------------------
data Statement = Less Expr Expr
               | LessEqual Expr Expr
               | Equal Expr Expr
               | More Expr Expr
               | MoreEqual Expr Expr
               | F
               | T


evalStatement :: Statement -> Store -> Bool
evalStatement (Less w z) s = (value w s) < (value z s)
evalStatement (LessEqual w z) s = (value w s) < (value z s) || (value w s) == (value z s)
evalStatement (Equal w z) s = (value w s) == (value z s)
evalStatement (More w z) s = (value w s) > (value z s)
evalStatement (MoreEqual w z) s = (value w s) > (value z s) || (value w s) == (value z s)
evalStatement F _ = False
evalStatement T _ = True


------------------------------- Language ------------------------------

data Lang = If Statement Lang
          | While Statement Lang
          | Assign Variable Expr

command :: Lang -> Store -> Store
command (Assign v e) s = update v s (Val (value e s))
command (If x l) s
  | evalStatement x s = command l s
  | otherwise = s
command (While x l) s
  | evalStatement x s = command (While x l) s'
  | otherwise = s
    where s' = command l s

------------------------------- Triple --------------------------------

triple :: Statement -> Statement -> Store -> Lang -> Bool
triple p q s l
  | evalStatement p s = evalStatement p s'
  | otherwise = False
    where s' = command l s



pre :: Statement
pre = More (Var X) (Val Zero)

post :: Statement
post = Equal (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))

com1 :: Lang
com1 = Assign (X) (Val (Succ Zero))

com2 :: Lang
com2 = While (Less (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))) (Assign (X) (Add (Var X) (Val (Succ Zero))))
