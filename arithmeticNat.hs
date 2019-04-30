------------------------------- Data types --------------------------------

data Nat = Zero | Succ Nat
           deriving (Eq, Ord, Show)

data Variable = U | V | W | X | Y | Z
                deriving (Eq, Ord, Show)

data SymVar = M | N | O | P
              deriving (Eq, Ord, Show)

data Expr = Val Nat
          | Var Variable
          | Sym SymVar
          | Mult Expr Expr
          | Div Expr Expr
          | Add Expr Expr
          | Sub Expr Expr
          deriving (Eq, Ord, Show)

data Op = EVALMULT Expr
        | EVALDIV Expr
        | EVALADD Expr
        | EVALSUB Expr
        | MULT Nat
        | DIV Nat
        | ADD Nat
        | SUB Nat



type Cont = [Op] -- control stacks

type State = [(Variable,Expr)] -- lookup table associates variables to nats

type States = [State]

------------------------------- State -----------------------------------

state1 :: State
state1 = [(U, Val (Succ Zero)),
         (V, Val (Zero)),
         (W, Sub (Sym M) (Sym N)),
         (X, Val (int2nat 21)),
         (Y, Val (int2nat 5)),
         (Z, Val (Zero))]

state2 = [(U, Val (Succ Zero)),
          (V, Val (Succ (Succ (Succ Zero)))),
          (W, Val (Succ Zero)),
          (X, Val (Succ (Succ Zero))),
          (Y, Val (Succ Zero)),
          (Z, Val (Zero))]

state3 = [(U, Val (Succ Zero)),
          (V, Val (Succ (Succ (Succ Zero)))),
          (W, Val (Succ Zero)),
          (X, Sym M),
          (Y, Sym N),
          (Z, Val (Succ Zero))]

states :: States
states = [state1,state2]


find :: Variable -> State -> Expr
find v s = head [n | (v',n) <- s, v == v']


delete :: Variable -> State -> State
delete v s  = [(v',n') | (v',n') <- s, v' /= v]


update :: Variable -> State -> Expr -> State
update _ [] n = []
update v (x:xs) n
  | (fst x) == v = (v,n):xs
  | otherwise = x:update v xs n

------------------------------- Arithmetic ------------------------------

-- Abstract Machine
eval :: Expr -> State -> Cont -> Nat
eval (Val n) s c = exec c s n
eval (Mult x y) s c = eval x s (EVALMULT y : c)
eval (Div x y) s c = eval x s (EVALDIV y : c)
eval (Add x y) s c = eval x s (EVALADD y : c)
eval (Sub x y) s c = eval x s (EVALSUB y : c)
eval (Var v) s c = eval (find v s) s c

exec :: Cont -> State -> Nat -> Nat
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

expr_sem :: Expr -> State -> Nat
expr_sem e s = eval e s []

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

stmt_sem :: Statement -> State -> Bool
stmt_sem (Less w z) s = (expr_sem w s) < (expr_sem z s)
stmt_sem (LessEqual w z) s = (expr_sem w s) < (expr_sem z s) || (expr_sem w s) == (expr_sem z s)
stmt_sem (Equal w z) s = (expr_sem w s) == (expr_sem z s)
stmt_sem (More w z) s = (expr_sem w s) > (expr_sem z s)
stmt_sem (MoreEqual w z) s = (expr_sem w s) > (expr_sem z s) || (expr_sem w s) == (expr_sem z s)
stmt_sem (Not stmt) s = not (stmt_sem stmt s)
stmt_sem (And stmt1 stmt2) s
  | stmt_sem stmt1 s = stmt_sem stmt2 s
  | otherwise = False
stmt_sem F _ = False
stmt_sem T _ = True

stmt_post :: Statements -> State -> Bool
stmt_post [] s = True
stmt_post (x:xs) s
  |stmt_sem x s = stmt_post xs s
  |otherwise = error "Post condition could not be reached"

stmt_sem_sym :: Statement -> State -> Bool
stmt_sem_sym (Equal (Var w) (Var z)) s = (simplify (Var w) s) == (simplify (Var z) s)
stmt_sem_sym (Equal (Sym w) (Var z)) s = (Sym w) == (simplify (Var z) s)
stmt_sem_sym (Equal (Var w) (Sym z)) s = (simplify (Var w) s) == (Sym z)
stmt_sem_sym (Equal w z) s = simplify w s == simplify z s
stmt_sem_sym T s = True
stmt_sem_sym F s = False

stmt_post_sym :: Statements -> State -> Bool
stmt_post_sym [] s = True
stmt_post_sym (x:xs) s
  |stmt_sem_sym x s = stmt_post_sym xs s
  |otherwise = error "Post condition could not be reached"

-- stmt_sem_sym (Equal (Sym M) (Add (Sym N) (Var V))) state

------------------------ Simplifying Expressions ---------------------------

simplify :: Expr -> State -> Expr
simplify (Add (Var v) x) s = simplify (Add (find v s) x) s
simplify (Add x (Var v)) s = simplify (Add x (find v s)) s
simplify (Add (Val x) (Val y)) s = Val (expr_sem (Add (Val x) (Val y)) s)
simplify (Add x (Sub y z)) s
  |z == x = simplify y s
  |y == z = simplify x s
  |x == y = simplify (Sub (Add x y) (z)) s
  |otherwise = Add (simplify x s) (simplify (Sub y z) s)
simplify (Add x y) s = Add (simplify x s) (simplify y s)
simplify (Sub (Var v) x) s = simplify (Sub (find v s) x) s
simplify (Sub x (Var v)) s = simplify (Sub x (find v s)) s
simplify (Sub (Val x) (Val y)) s = Val (expr_sem (Sub (Val x) (Val y)) s)
simplify (Sub x (Add y z)) s
  |z == x = simplify y s
  |x == y = simplify z s
  |otherwise = Sub (simplify x s) (simplify (Add y z) s)
simplify (Sub x y) s = Sub (simplify x s) (simplify y s)
simplify (Val x) s = (Val x)
simplify (Var x) s = simplify (find x s) s
simplify (Sym x) s = (Sym x)
simplify x s = x

hasSym :: Expr -> State -> Bool
hasSym (Sym x) s = True
hasSym (Add x y) s = True
hasSym (Sub x y) s = True
hasSym (Val x) s = False
hasSym e s = False

--simplify (Add (Add (Sym N) (Val (Succ Zero))) (Sym M))

------------------------------- Language ------------------------------

-- data a *->* b = Left a | Right b

data Com = Assign Variable Expr
          | If Statement Com Com
          | While Statement Com
          | Seq Com Com

com_sem :: Com -> State -> State
com_sem (Assign v e) s
  | hasSym (simplify e s) s = update v s (simplify e s)
  | otherwise = update v s (Val (expr_sem e s))
com_sem (If x c1 c2) s
  | stmt_sem x s = com_sem c1 s
  | otherwise = com_sem c2 s
com_sem (While x c) s
  | stmt_sem x s = com_sem (While x c) s'
  | otherwise = s
    where s' = com_sem c s
com_sem (Seq c1 c2) s = com_sem c1 s'
    where s' = com_sem c2 s

--com_sem (Assign (V) (Sub (Sym M) (Sym N))) state

------------------------------- h_sem --------------------------------

h_sem :: Statements -> Com -> Statements -> State -> Bool
h_sem [] c q s = stmt_post q s'
  where s' = com_sem c s
h_sem p@(x:xs) c q s
  |stmt_sem x s = h_sem xs c q s
  |otherwise = False

h_sem_recursion :: Statements -> Com -> Statements -> States -> Bool
h_sem_recursion p c q [] = True
h_sem_recursion p c q (x:xs)
  | h_sem p c q x  = h_sem_recursion p c q xs
  | otherwise = h_sem_recursion p c q xs

h_sem_sym :: Statements -> Com -> Statements -> State -> Bool
h_sem_sym [] c q s = stmt_post_sym q s'
  where s' = com_sem c s
h_sem_sym p@(x:xs) c q s
  | stmt_sem_sym x s = h_sem_sym xs c q s
  | otherwise = False

h_sem1 :: (State -> Bool) -> (State -> State) -> (State -> Bool) -> State -> Bool
h_sem1 p c q s
  | p s = q s'
  | otherwise = False
    where s' = c s

--test (stmt_sem pre_swap) (com_sem swap_vars) (stmt_sem post_swap) state

-- h_sem [pre_swap,pre_swap2] [post_swap,post_swap2] state swap_vars
-- h_sem_sym [T] [Equal (Sym M) (Add (Sym N) (Var V))] state (Assign (V) (Sub (Sym M) (Sym N)))

------------------------------- Variables --------------------------------

-- stmt_sem (Equal (Var X) (Mult (Var Y) (Val (int2nat 4)))) state
-- h_sem_recursion [pre_div, pre_div2] div_vars [post_div] states

-- Swap_Vars pre and post
pre_swap :: Statement
pre_swap = Equal (Var X) (Val (Succ (Succ Zero)))

pre_swap2 :: Statement
pre_swap2 = Equal (Var Y) (Val (Succ Zero))

post_swap :: Statement
post_swap = Equal (Var Y) (Val (Succ (Succ Zero)))

post_swap2 :: Statement
post_swap2 = Equal (Var X) (Val (Succ Zero))

swap_vars :: Com
swap_vars = Seq (Assign (Y) (Var Z)) (Seq (Assign (X) (Var Y)) (Assign (Z) (Var X)))

-- h_sem_recursion [pre_swap,pre_swap2] swap_vars [post_swap,post_swap2] states

-- Swap vars sym variables
pre_swap_sym :: Statement
pre_swap_sym = Equal (Var X) (Sym M)

pre_swap_sym2 :: Statement
pre_swap_sym2 = Equal (Var Y) (Sym N)

post_swap_sym :: Statement
post_swap_sym = Equal (Var X) (Sym N)

post_swap_sym2 :: Statement
post_swap_sym2 = Equal (Var Y) (Sym M)

swap_vars_sym :: Com
swap_vars_sym = Seq (Assign (Y) (Var V)) (Seq (Assign (X) (Var Y)) (Assign (Z) (Var X)))

-- h_sem_sym [pre_swap_sym,pre_swap_sym2] [post_swap_sym,post_swap_sym2] state3 swap_vars_sym

-- Divide x by y pre and post
pre_div :: Statement
pre_div = More (Var Y) (Val Zero)

pre_div2 :: Statement
pre_div2 = More (Var X) (Var Y)

post_div :: Statement
post_div = Equal (Var X) (Mult (Var V) (Var Y))

div_vars :: Com
div_vars = Assign (V) (Div (Var X) (Var Y))


-- Divide using while loop
div_while :: Com
div_while = Seq (If (And (Not (Equal (Var Z) (Val Zero))) (Less (Var Z) (Var Y))) (Assign (U) (Var Z)) (Assign (U) (Val Zero))) (Seq (While (MoreEqual (Var Z) (Var Y)) (Seq (Assign (V) (Add (Var V) (Val (Succ Zero)))) (Assign (Z) (Sub (Var Z) (Var Y))))) (Seq (Assign (Z) (Var X)) (Assign (V) (Val Zero))))

post_div_while :: Statement
post_div_while = Equal (Var X) (Add (Mult (Var V) (Var Y)) (Var U))


-- Test commands
eg_assign :: Com
eg_assign = Assign (X) (Val (Succ Zero))

eg_while :: Com
eg_while = While (Less (Var X) (Val (Succ (Succ (Succ (Succ Zero)))))) (Assign (X) (Add (Var X) (Val (Succ Zero))))

eg_seq :: Com
eg_seq = Seq (Assign (Z) (Add (Var Z) (Var V))) (Seq (Assign (Z) (Add (Var Y) (Var Z))) (Assign (V) (Add (Var V) (Var Y))))

eg_if :: Com
eg_if = If (Equal (Var X) (Val (Succ(Zero)))) (Assign (X) (Val (Zero))) (If (Less (Var U) (Var V)) (Assign (V) (Val (Succ Zero))) (Assign (V) (Val (Succ(Succ Zero) ))))
