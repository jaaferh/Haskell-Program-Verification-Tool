type Assoc k v = [(k,v)]

data Prop = Const Bool
          | Var Char
          | Not Prop
          | And Prop Prop
          | Imply Prop Prop


p1 :: Prop
p1 = And (Var 'A') (Not (Var 'A'))
