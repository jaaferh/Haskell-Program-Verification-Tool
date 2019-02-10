------------------------------- Arithmetic ------------------------------
data Expr = Val Int
          | Div Expr Expr
          | Mult Expr Expr
          | Add Expr Expr
          | Sub Expr Expr -- expressions

data Op = EVALDIV Expr
        | EVALMULT Expr
        | EVALADD Expr
        | EVALSUB Expr
        | DIV Int
        | MULT Int
        | ADD Int
        | SUB Int -- operations

type Cont = [Op] -- control stacks


-- Abstract Machine
eval :: Expr -> Cont -> Int
eval (Val n) c = exec c n
eval (Add x y) c = eval x (EVALADD y : c)
eval (Mult x y) c = eval x (EVALMULT y : c)
eval (Div x y) c = eval x (EVALDIV y : c)
eval (Sub x y) c = eval x (EVALSUB y : c)

exec :: Cont -> Int -> Int
exec [] n = n
exec (EVALDIV y : c) n = eval y (DIV n : c)
exec (EVALMULT y : c) n = eval y (MULT n : c)
exec (EVALADD y : c) n = eval y (ADD n : c)
exec (EVALSUB y : c) n = eval y (SUB n : c)
exec (DIV n : c) m = exec c (safeDiv n m)
exec (MULT n : c) m = exec c (n*m)
exec (ADD n : c) m = exec c (n+m)
exec (SUB n : c) m = exec c (n-m)



safeDiv :: Int -> Int -> Int
safeDiv _ 0 = 0
safeDiv n m = (n `div` m)

value :: Expr -> Int
value e = eval e []


validationAdd :: Expr -> Expr -> Expr -> Bool
validationAdd a b e
          | (value a) + (value b) == value e = True
          | otherwise = False

validationMult :: Expr -> Expr -> Expr -> Bool
validationMult a b e
          | (value a) * (value b) == value e = True
          | otherwise = False


------------------------------- Equalities ------------------------------
data Statement = Less Expr
               | LessEqual Expr
               | Equal Expr
               | More Expr
               | MoreEqual Expr
               | F
               | T


evalStatement :: Int -> Statement -> Bool
evalStatement i (Less e) = i < (value e)
evalStatement i (LessEqual e) = i < (value e) || i == (value e)
evalStatement i (Equal e) = i == (value e)
evalStatement i (More e) = i > (value e)
evalStatement i (MoreEqual e) = i > (value e) || i == (value e)
evalStatement _ (F) = False
evalStatement _ (T) = True

checkTriple :: Int -> Statement -> Expr -> Statement -> Bool
checkTriple x p s q
  | evalStatement x p = evalStatement x' q
  | otherwise = False
    where x' = value s


a :: Int
a = 3

preCon :: Statement
preCon = Equal (Val 1)

postCon :: Statement
postCon = Equal (Val 2)

program :: Expr
program = Add (Val a) (Val 1)
