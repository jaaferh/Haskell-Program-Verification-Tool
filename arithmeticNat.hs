------------------------------- Arithmetic ------------------------------
data Nat = Zero | Succ Nat
        deriving (Eq, Ord, Show, Read)


data Expr = Val Nat
          | U Var
          | Mult Expr Expr
          | Add Expr Expr
          | Sub Expr Expr

data Op = EVALMULT Expr
        | EVALADD Expr
        | EVALSUB Expr
        | MULT Nat
        | ADD Nat
        | SUB Nat

type Cont = [Op] -- control stacks



-- Abstract Machine
eval :: Expr -> Cont -> Nat
eval (Val n) c = exec c n
eval (Mult x y) c = eval x (EVALMULT y : c)
eval (Add x y) c = eval x (EVALADD y : c)
eval (Sub x y) c = eval x (EVALSUB y : c)

exec :: Cont -> Nat -> Nat
exec [] n = n
exec (EVALMULT y : c) n = eval y (MULT n : c)
exec (EVALADD y : c) n = eval y (ADD n : c)
exec (EVALSUB y : c) n = eval y (SUB n : c)
exec (MULT n : c) m = exec c (mul n m)
exec (ADD n : c) m = exec c (add n m)
exec (SUB n : c) m = exec c (sub n m)


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


-- nat2int :: Nat -> Int
-- nat2int Zero = 0
-- nat2int (Succ n) = 1 + nat2int n
--
-- int2nat :: Int -> Nat
-- int2nat 0 = Zero
-- int2nat n = Succ (int2nat (n-1))


value :: Expr -> Nat
value e = eval e []


validationAdd :: Expr -> Expr -> Expr -> Bool
validationAdd a b e
          | add (value a) (value b) == value e = True
          | otherwise = False

validationMult :: Expr -> Expr -> Expr -> Bool
validationMult a b e
          | mul (value a) (value b) == value e = True
          | otherwise = False

validationSub :: Expr -> Expr -> Expr -> Bool
validationSub a b e
          | sub (value a) (value b) == value e = True
          | otherwise = False

------------------------------- Equalities ------------------------------
data Statement = Less Expr
               | LessEqual Expr
               | Equal Expr
               | More Expr
               | MoreEqual Expr
               | F
               | T


evalStatement :: Nat -> Statement -> Bool
evalStatement i (Less e) = i < (value e)
evalStatement i (LessEqual e) = i < (value e) || i == (value e)
evalStatement i (Equal e) = i == (value e)
evalStatement i (More e) = i > (value e)
evalStatement i (MoreEqual e) = i > (value e) || i == (value e)
evalStatement _ (F) = False
evalStatement _ (T) = True

checkTriple :: Nat -> Statement -> Expr -> Statement -> Bool
checkTriple x p s q
  | evalStatement x p = evalStatement x' q
  | otherwise = False
    where x' = value s


a :: Nat
a = (Succ Zero)

preCon :: Statement
preCon = Equal (Val (Succ Zero))

postCon :: Statement
postCon = Equal (Val (Succ (Succ Zero)))

program :: Expr
program = Add (Val a) (Val (Succ Zero))
