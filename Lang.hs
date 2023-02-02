module Lang where

import Data.Maybe
import Control.Monad.State.Lazy hiding (lift)

newtype TVarName = TVarName String deriving Eq
newtype TExVarName = TExVarName String deriving Eq
data Monotype = MonoUnit | MonoVar TVarName | MonoExVar TExVarName | MonoFunc Monotype Monotype deriving Eq
data Type = TUnit | TVar TVarName | TExVar TExVarName | TForall TVarName Type | TFunc Type Type deriving Eq

fv t = fv_inner [] t --TODO: Can do a make-unique pass
fv_inner bound TUnit = []
fv_inner bound (TVar x) = if Left x `elem` bound then [] else [Left x]
fv_inner bound (TExVar x) = if Right x `elem` bound then [] else [Right x]
fv_inner bound (TFunc x y) = fv_inner bound x ++ fv_inner bound y
fv_inner bound (TForall x y) = fv_inner (Left x : bound) y

lift MonoUnit = TUnit
lift (MonoVar alpha) = TVar alpha
lift (MonoExVar alpha) = TExVar alpha
lift (MonoFunc tau sigma) = TFunc (lift tau) (lift sigma)

data ContextEntry = HasVar TVarName | HasAnno TVarName Type
    | HasExistentialUnsolved TExVarName | HasExistentialSolved TExVarName Monotype
    | Marker TExVarName deriving Eq
newtype Context = Context [ContextEntry] deriving Eq
uncontext (Context c) = c
ctxcons e c = Context (e : uncontext c)
infixr 4 `ctxcons`
{- 
   Note: since the paper only works with APpending to contexts and recurses to the LEFT,
   it makes more sense to implement everything as the reverse,
   PREpending to contexts and recursing on the RIGHT.
-}

data Term = Var String | Unit | Lam String Term | App Term Term | Anno Term Type

dom (Context []) = []
dom (Context (c : cs)) = case c of
    HasVar alpha -> Left alpha : dom (Context cs) 
    HasAnno alpha _ -> Left alpha : dom (Context cs)
    HasExistentialUnsolved alpha_hat -> Right alpha_hat : dom (Context cs)
    HasExistentialSolved alpha_hat _ -> Right alpha_hat : dom (Context cs)
    Marker _ -> dom (Context cs)

wf_ctx :: Context -> Bool
wf_ctx (Context []) = True
wf_ctx (Context (x:cs)) = let c' = Context cs in case x of
    HasVar alpha                       -> wf_ctx c' && not (Left alpha `elem` dom c')
    HasAnno alpha ty                   -> wf_ctx c' && not (Left alpha `elem` dom c') && wf c' ty
    HasExistentialUnsolved alpha_hat   -> wf_ctx c' && not (Right alpha_hat `elem` dom c')
    HasExistentialSolved alpha_hat tau -> wf_ctx c' && not (Right alpha_hat `elem` dom c') && wf c' (lift tau)

wf :: Context -> Type -> Bool
wf _ TUnit = True
wf c (TVar alpha) = case hole c (HasVar alpha) of Just _ -> True ; _ -> False
wf c (TFunc a b)  = wf c a && wf c b
wf c (TForall alpha a) = wf (HasVar alpha `ctxcons` c) a
wf c (TExVar alpha_hat) = (case hole c (HasExistentialUnsolved alpha_hat) of Just _ -> True ; _ -> False) ||
                          (any (\e -> case e of (HasExistentialSolved ex _) -> ex == alpha_hat ; _ -> False) (uncontext c))

hole :: Context -> ContextEntry -> Maybe (Context, ContextEntry, Context)
hole = hole_inner []

hole_inner acc (Context []) _ = Nothing
hole_inner acc (Context (e : es)) entry = if e == entry then Just (Context $ reverse acc, entry, Context es) else hole_inner (e : acc) (Context es) entry

findVar _ (Context []) = Nothing
findVar x@(Right exvarname) (Context (HasExistentialSolved exvar var:cs)) = if exvarname == exvar then Just $ HasExistentialSolved exvar var else findVar x (Context cs)
findVar x@(Right exvarname) (Context (HasExistentialUnsolved exvar:cs)) = if exvarname == exvar then Just $ HasExistentialUnsolved exvar else findVar x (Context cs)
findVar x@(Left varname) (Context (HasVar var:cs)) = if varname == var then Just $ HasVar var else findVar x (Context cs)
findVar x@(Left varname) (Context (HasAnno var ty:cs)) = if varname == var then Just $ HasAnno var ty else findVar x (Context cs)
findVar x (Context (c : cs)) = findVar x (Context cs)

ignore_to_marker marker c@(Context []) = c
ignore_to_marker marker (Context (Marker m : cs)) | marker == m = Context cs
ignore_to_marker marker (Context (c : cs)) = ignore_to_marker marker (Context cs)

apply :: Context -> Type -> Type
apply gamma x@(TExVar alpha_hat) = case findVar (Right alpha_hat) gamma of
    Just (HasExistentialSolved _ monoty) -> apply gamma (lift monoty)
    _ -> x
apply gamma (TFunc a b) = TFunc (apply gamma a) (apply gamma b)
apply gamma (TForall alpha a) = TForall alpha (apply gamma a)
apply _ x = x

subst = undefined

newexvar i = TExVarName $ "@" ++ show i

-- If it is a subtype, will be a Just. State for creating fresh variables.
subty :: Context -> Type -> Type -> State Int (Maybe Context)
-- <:Var
subty gamma (TVar alpha) (TVar beta) = return $ if alpha == beta && isJust (hole gamma (HasVar alpha))
    then Just gamma
    else Nothing
-- <:Unit
subty gamma TUnit TUnit = return $ Just gamma
-- <:Exvar
subty gamma (TExVar alpha_hat) (TExVar beta_hat) = return $
    if alpha_hat == beta_hat && isJust (hole gamma (HasExistentialUnsolved alpha_hat)) --TODO: Might be dom membership?
    then Just gamma else Nothing
-- <:->
subty gamma (TFunc a1 a2) (TFunc b1 b2) = 
    subty gamma b1 a1 >>= \st' -> case st' of
        Just theta -> subty theta (apply theta a2) (apply theta b2)
        Nothing -> return Nothing
-- <:forallL
subty gamma (TForall alpha a) b = do
    i <- get
    put (i+1)
    let alpha_hat = newexvar i
    fmap (fmap (ignore_to_marker alpha_hat)) $ subty (HasExistentialUnsolved alpha_hat `ctxcons` Marker alpha_hat `ctxcons` gamma) (subst alpha_hat a) b
-- <:forallR
subty gamma a (TForall alpha b) = 
    flip fmap (subty (HasVar alpha `ctxcons` gamma) a b) $ (>>= \deltaalphatheta -> fmap (\(a, b, c) -> c) $ hole deltaalphatheta (HasVar alpha))
-- <:InstantiateL
subty gamma (TExVar alpha_hat) a = if not (Right alpha_hat `elem` fv a)
    then case hole gamma (HasExistentialUnsolved alpha_hat) of
        Just (cl, HasExistentialUnsolved _, cr) -> fmap Just $ instl (cl, alpha_hat, cr) a
        Nothing -> return Nothing
    else return Nothing
-- <:InstantiateR
subty gamma a (TExVar alpha_hat) = if not (Right alpha_hat `elem` fv a)
    then case hole gamma (HasExistentialUnsolved alpha_hat) of
        Just (cl, HasExistentialUnsolved _, cr) -> fmap Just $ instr (cl, alpha_hat, cr) a
        Nothing -> return Nothing
    else return Nothing
subty _ _ _ = return Nothing

instl :: (Context, TExVarName, Context) -> Type -> State Int Context
-- InstLSolve
instl (cl, alpha_hat, cr) t@(TVar tau) | wf cr t = return $ Context (uncontext cl ++ HasExistentialSolved alpha_hat (MonoVar tau) : uncontext cr)
-- InstLReach
instl (cl, alpha_hat, cr) b@(TExVar beta_hat) = let (cll, beta, clr) = fromJust (hole cl (HasExistentialUnsolved beta_hat)) in
    return $ Context (uncontext cll ++ HasExistentialSolved beta_hat (MonoExVar alpha_hat) : uncontext clr ++ HasExistentialUnsolved alpha_hat : uncontext cr)
-- InstLArr
instl (cl, alpha_hat, cr) (TArr a1 a2) = do
    i <- get
    let alpha_hat1 = newexvar i
    let alpha_hat2 = newexvar (i + 1)
    put (i + 2)
    theta <- instr (HasExistentialUnsolved alpha_hat1 `ctxcons` cl, alpha_hat1, HasExistentialSolved alpha_hat (MonoFunc (MonoExVar alpha_hat1) (MonoExVar alpha_hat2)) `ctxcons` cr) a1
    instl theta (apply theta a2)
instr :: (Context, TExVarName, Context) -> Type -> State Int Context
instr = undefined


{-
subst tau alpha ty = 
    case ty of
         | TVar s => if s == alpha then TVar tau else TVar s
         | Forall x y => if x == alpha then ty else Forall x (subst tau alpha y)
         | Func a b => Func (subst tau alpha a) (subst tau alpha b)
         | _ => ty


sub :: Context -> Type -> Type -> Bool
sub (Context c) (TVar a) (TVar b) = a == b && (Left a `elem` c)
sub _ CUnit CUnit = true
sub c (Func a1 a2) (Func b1 b2) = sub c b1 a1 && sub c a2 b2
sub c (Forall alpha a) b = wf c 
-}
