------------------------------- Data types --------------------------------

data Nat = Zero | Succ Nat
           deriving (Eq, Ord, Show, Read)

data Variable = U | V | W | X | Y | Z
                deriving (Eq, Ord, Show, Read)

data SymVar = M | N | O | P
              deriving (Eq, Ord, Show, Read)

data Expr = Val Nat
          | Var Variable
          | Sym SymVar
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
         (W, Sub (Sym M) (Sym N)),
         (X, Val (int2nat 20)),
         (Y, Val (int2nat 5)),
         (Z, Val (Zero))]

store2 = [(U, Val (Succ Zero)),
          (V, Val (Succ (Succ (Succ Zero)))),
          (W, Val (Succ Zero)),
          (X, Val (Succ (Succ Zero))),
          (Y, Val (Zero)),
          (Z, Val (Succ Zero))]

store3 = [(U, Val (Succ Zero)),
          (V, Val (Succ (Succ (Succ Zero)))),
          (W, Val (Succ Zero)),
          (X, Sym M),
          (Y, Sym N),
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

-- This function is exactly the same as sub, but preserves the counter
d_sub :: Nat -> Nat -> Nat -> Nat -- number, factor, counter
d_sub Zero _ _ = Zero
d_sub n Zero _ = n
d_sub (Succ n) (Succ m) c = d_sub n m c


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
               | Not Statement
               | And Statement Statement
               | F
               | T

type Statements = [Statement]

evalStatement :: Statement -> Store -> Bool
evalStatement (Less w z) s = (value w s) < (value z s)
evalStatement (LessEqual w z) s = (value w s) < (value z s) || (value w s) == (value z s)
evalStatement (Equal w z) s = (value w s) == (value z s)
evalStatement (More w z) s = (value w s) > (value z s)
evalStatement (MoreEqual w z) s = (value w s) > (value z s) || (value w s) == (value z s)
evalStatement (Not stmt) s = not (evalStatement stmt s)
evalStatement (And stmt1 stmt2) s
  | evalStatement stmt1 s = evalStatement stmt2 s
  | otherwise = False
evalStatement F _ = False
evalStatement T _ = True

evalPost :: Statements -> Store -> Bool
evalPost [] s = True
evalPost (x:xs) s
  |evalStatement x s = evalPost xs s
  |otherwise = error "Post condition could not be reached"

evalSym :: Statement -> Store -> Bool
evalSym (Equal (Var w) (Var z)) s = (simplify (Var w) s) == (simplify (Var z) s)
evalSym (Equal (Sym w) (Var z)) s = (Sym w) == (simplify (Var z) s)
evalSym (Equal (Var w) (Sym z)) s = (simplify (Var w) s) == (Sym z)
evalSym (Equal w z) s = simplify w s == simplify z s

simpPost :: Statements -> Store -> Bool
simpPost [] s = True
simpPost (x:xs) s
  |evalSym x s = simpPost xs s
  |otherwise = error "Post condition could not be reached"

-- evalSym (Equal (Sym M) (Add (Sym N) (Var V))) store

------------------------ Simplifying Expressions ---------------------------

simplify :: Expr -> Store -> Expr
simplify (Add (Var v) x) s = simplify (Add (find v s) x) s
simplify (Add x (Var v)) s = simplify (Add x (find v s)) s
simplify (Add (Val x) (Val y)) s = Val (value (Add (Val x) (Val y)) s)
simplify (Sub (Var v) x) s = simplify (Sub (find v s) x) s
simplify (Sub x (Var v)) s = simplify (Sub x (find v s)) s
simplify (Sub (Val x) (Val y)) s = Val (value (Sub (Val x) (Val y)) s)
simplify (Add x (Sub y v)) s
  |v == x = simplify y s
  |y == v = simplify x s
  |otherwise = Val Zero
simplify (Sub x (Add y z)) s
  |z == x = simplify y s
  |x == y = simplify z s
  |otherwise = Val Zero
simplify (Val x) s = (Val x)
simplify (Var x) s = simplify (find x s) s
simplify (Sym x) s = (Sym x)
simplify x s = x

hasSym :: Expr -> Store -> Bool
hasSym (Sym x) s = True
hasSym (Add x y) s = True
hasSym (Sub x y) s = True
hasSym (Val x) s = False
hasSym e s = False

------------------------------- Language ------------------------------

-- data a *->* b = Left a | Right b

data Lang = Assign Variable Expr
          | If Statement Lang Lang
          | While Statement Lang
          | Seq Lang Lang

inter :: Lang -> Store -> Store
-- inter (Assign v e) s = update v s (Val (value e s))
inter (Assign v e) s
  | hasSym (simplify e s) s = update v s (simplify e s)
  | otherwise = update v s (Val (value e s))
inter (If x l1 l2) s
  | evalStatement x s = inter l1 s
  | otherwise = inter l2 s
inter (While x l) s
  | evalStatement x s = inter (While x l) s'
  | otherwise = s
    where s' = inter l s
inter (Seq l1 l2) s = inter l1 s'
  where s' = inter l2 s

--inter (Assign (V) (Sub (Sym M) (Sym N))) store

------------------------------- Triple --------------------------------

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
  | otherwise = triple_recursion p q xs l

triple_sym :: Statements -> Statements -> Store -> Lang -> Bool
triple_sym [] q s l = simpPost q s'
  where s' = inter l s
triple_sym p@(x:xs) q s l
  |evalSym x s = triple_sym xs q s l
  |otherwise = False

-- triple_sym [T] [Equal (Sym M) (Add (Sym N) (Var V))] store (Assign (V) (Sub (Sym M) (Sym N)))

------------------------------- Variables --------------------------------

--evalStatement (Equal (Var X) (Mult (Var Y) (Val (int2nat 4)))) store
-- triple_recursion [pre_div, pre_div2] [post_div] stores div_vars

-- Swap_Vars pre and post
pre_swap :: Statement
pre_swap = Equal (Var X) (Val (Succ (Succ Zero)))

pre_swap2 :: Statement
pre_swap2 = Equal (Var Y) (Val (Succ Zero))

post_swap :: Statement
post_swap = Equal (Var Y) (Val (Succ (Succ Zero)))

post_swap2 :: Statement
post_swap2 = Equal (Var X) (Val (Succ Zero))

swap_vars :: Lang
swap_vars = Seq (Assign (Y) (Var Z)) (Seq (Assign (X) (Var Y)) (Seq (Assign (V) (Var Y)) (Assign (Z) (Var X))))


-- Swap vars sym variables
pre_swap_sym :: Statement
pre_swap_sym = Equal (Var X) (Sym M)

pre_swap_sym2 :: Statement
pre_swap_sym2 = Equal (Var Y) (Sym N)

post_swap_sym :: Statement
post_swap_sym = Equal (Var X) (Sym N)

post_swap_sym2 :: Statement
post_swap_sym2 = Equal (Var Y) (Sym M)

swap_vars_sym :: Lang
swap_vars_sym = Seq (Assign (Y) (Var V)) (Seq (Assign (X) (Var Y)) (Assign (V) (Var X)))

-- triple_sym [pre_swap_sym,pre_swap_sym2] [post_swap_sym,post_swap_sym2] store3 swap_vars_sym

-- Divide x by y pre and post
pre_div :: Statement
pre_div = More (Var Y) (Val Zero)

pre_div2 :: Statement
pre_div2 = More (Var X) (Var Y)

post_div :: Statement
post_div = Equal (Var X) (Mult (Var V) (Var Y))

div_vars :: Lang
div_vars = Assign (V) (Div (Var X) (Var Y))


-- Divide using while loop
div_while :: Lang
div_while = Seq (If (And (Not (Equal (Var Z) (Val Zero))) (Less (Var Z) (Var Y))) (Assign (U) (Var Z)) (Assign (U) (Val Zero))) (Seq (While (MoreEqual (Var Z) (Var Y)) (Seq (Assign (V) (Add (Var V) (Val (Succ Zero)))) (Assign (Z) (Sub (Var Z) (Var Y))))) (Seq (Assign (Z) (Var X)) (Assign (V) (Val Zero))))

post_div_while :: Statement
post_div_while = Equal (Var X) (Add (Mult (Var V) (Var Y)) (Var U))


-- Test commands
eg_assign :: Lang
eg_assign = Assign (X) (Val (Succ Zero))

eg_while :: Lang
eg_while = While (Less (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))) (Assign (X) (Add (Var X) (Val (Succ Zero))))

eg_seq :: Lang
eg_seq = Seq (Assign (Z) (Add (Var Z) (Var V))) (Seq (Assign (Z) (Add (Var Y) (Var Z))) (Assign (V) (Add (Var V) (Var Y))))

eg_if :: Lang
eg_if = If (Equal (Var X) (Val (Succ(Zero)))) (Assign (X) (Val (Zero))) (If (Less (Var U) (Var V)) (Assign (V) (Val (Succ Zero))) (Assign (V) (Val (Succ(Succ Zero) ))))
