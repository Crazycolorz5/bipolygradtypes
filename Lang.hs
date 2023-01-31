module Lang where

data Monotype = MonoUnit | MonoVar String | MonoFunc Monotype Monotype deriving Eq
data Type = TUnit | TVar String | Forall String Type | Func Type Type deriving Eq
newtype Context = Context ([Either String (String, Type)]) deriving Eq

data Term = Var String | Unit | Lam String Term | App Term Term | Anno Term Type

subst tau alpha ty = 
    case ty of
         | TVar s => if s == alpha then TVar tau else TVar s
         | Forall x y => if x == alpha then ty else Forall x (subst tau alpha y)
         | Func a b => Func (subst tau alpha a) (subst tau alpha b)
         | _ => ty

wf :: Context -> Type -> Bool
wf _ TUnit = true
wf (Context c) (TVar a) = (Left a) `elem` c
wf (Context c) (Forall alpha a) = wf (Context $ Left alpha : c) a
wf c (Func a b)  = wf c a && wf c b

sub :: Context -> Type -> Type -> Bool
sub (Context c) (TVar a) (TVar b) = a == b && (Left a `elem` c)
sub _ CUnit CUnit = true
sub c (Func a1 a2) (Func b1 b2) = sub c b1 a1 && sub c a2 b2
sub c (Forall alpha a) b = wf c 
