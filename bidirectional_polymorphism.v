From Coq Require Import Strings.String.
Open Scope string_scope.

Inductive type := 
  | TUnit
  | TVar (alpha : string)
  | TForall (alpha : string) (a : type)
  | TFunc (a : type) (b : type)
.

Scheme Equality for type.

Fixpoint subst tau alpha type := match type with
  | TUnit => TUnit
  | TVar x => if string_dec x alpha then TVar tau else TVar x
  | TForall x a => if string_dec x alpha then TForall x a else TForall x (subst tau alpha a)
  | TFunc a b => TFunc (subst tau alpha a) (subst tau alpha b)
end.

Example example_type := TFunc TUnit (TForall "x" (TVar "X")) : type.

Inductive term :=
  | EVar (x : string)
  | EUnit
  | ELam (x : string) (e : term)
  | EApp (e1 : term) (e2 : term)
  | EAnno (e : term) (a : type)
.

Example example_term := ELam "x" (EApp (EVar "f") (EVar "x")) : term.

Inductive context :=
  | EmptyContext
  | HasVar (alpha : string) (c : context)
  | HasAnno (anno : (string * type)) (c : context)
.

Fixpoint varInContext a c := match c with
  | EmptyContext => false
  | HasVar alpha c' => if string_dec alpha a then true else varInContext a c'
  | HasAnno _ c' => varInContext a c'
end.

Fixpoint annoInContext a ty c := match c with
  | EmptyContext => false
  | HasVar _ c' => annoInContext a ty c'
  | HasAnno (b, ty') c' => if string_dec a b then type_beq ty ty' else annoInContext a ty c'
end.

Inductive wf (c : context) : type -> Prop :=
  | DeclUvarWF alpha : varInContext alpha c = true -> wf c (TVar alpha)
  | DeclUnitWF : wf c TUnit
  | DeclArrowWF a b : wf c a -> wf c b -> wf c (TFunc a b)
  | DeclForallWF alpha a: wf (HasVar alpha c) a -> wf c (TForall alpha a)
.

Example wf_ex : wf (HasVar "x" EmptyContext) (TVar "x").
Proof.
  apply (DeclUvarWF). reflexivity.
Qed.

Inductive subty (c : context) : type -> type -> Prop :=
  | STVar alpha: (varInContext alpha c) = true -> subty c (TVar alpha) (TVar alpha)
  | STUnit : subty c TUnit TUnit
  | STFunc a1 a2 b1 b2 : subty c b1 a1 -> subty c a2 b2 -> 
      subty c (TFunc a1 a2) (TFunc b1 b2)
  | STForallL (tau alpha : string) (a b : type):
      wf c (TVar tau) -> subty c (subst tau alpha a) b ->
      subty c (TForall alpha a) b
  | STForallR beta a b:
      subty (HasVar beta c) a b -> subty c a (TForall beta b)
.

Inductive Checks (c : context) : term -> type -> Prop :=
  | Decl1ICheck : Checks c EUnit TUnit
  | DeclSub e a b : Synthesizes c e a -> subty c a b -> Checks c e b
  | DeclForallI e a alpha : Checks (HasVar alpha c) e a -> Checks c e (TForall alpha a)
  | DeclLamICheck x e a b : Checks (HasAnno (x, a) c) e b -> Checks c (ELam x e) (TFunc a b)
  with Synthesizes (c : context) : term -> type -> Prop :=
  | DeclVar (x : string) a : annoInContext x a c = true -> Synthesizes c (EVar x) a 
  | DeclAnno (e : term) (a : type) : wf c a -> Checks c e a -> Synthesizes c (EAnno e a) a
  | Decl1ISynth : Synthesizes c EUnit TUnit
  | DeclLamISynth x e sigma tau : wf c (TFunc sigma tau) -> Checks (HasAnno (x, sigma) c) e tau -> Synthesizes c (ELam x e) (TFunc sigma tau)
  | DeclLamE e1 e2 a b : Synthesizes c e1 a -> AppliesTo c a e2 b -> Synthesizes c (EApp e1 e2) b
  with AppliesTo (c : context) : type -> term -> type -> Prop :=
  | DeclForallApp tau alpha e a b : wf c (TVar tau) -> AppliesTo c (subst tau alpha a) e b -> AppliesTo c (TForall alpha a) e b
  | DeclLamApp e a b : Checks c e a -> AppliesTo c (TFunc a b) e b
.

Definition identityFunction := EAnno (ELam "x" (EVar "x")) (TForall "a" (TFunc (TVar "a") (TVar "a"))).

Lemma identityFunctionLemma: forall c, Synthesizes c identityFunction (TForall "a" (TFunc (TVar "a") (TVar "a"))).
Proof. 
  intros.
  eapply DeclAnno.
    + apply DeclForallWF. apply DeclArrowWF; apply DeclUvarWF; reflexivity.
    + eapply DeclForallI. apply DeclLamICheck.
      eapply DeclSub with (TVar "a").
      * apply DeclVar. reflexivity.
      * apply STVar. reflexivity.
Qed.

Example identityFunctionType: Checks EmptyContext identityFunction (TForall "a" (TFunc (TVar "a") (TVar "a"))).
Proof.
  unfold identityFunction.
  eapply DeclSub.
  - apply identityFunctionLemma.
  - eapply STForallR. apply (STForallL _ "a").
    + apply DeclUvarWF. reflexivity.
    + apply STFunc.
      * simpl. apply STVar. reflexivity.
      * simpl. apply STVar. reflexivity.
Qed. 


Definition identityProgram := 
  EApp identityFunction 
       (EVar "y").

Example identityProgramType: Checks (HasAnno ("y", TVar "b") (HasVar "b" EmptyContext))
                             identityProgram (TVar "b").
Proof.
  unfold identityProgram. eapply DeclSub.
  - eapply (DeclLamE _ _ _ _ (TVar "b")).
    * apply identityFunctionLemma.
    * eapply DeclForallApp with "b".
      + apply DeclUvarWF. reflexivity.
      + eapply DeclLamApp. simpl. eapply DeclSub with (TVar "b").
        { apply DeclVar. reflexivity. }
        { apply STVar. reflexivity. }
  - apply STVar. reflexivity.
Qed.



