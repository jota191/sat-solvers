

%if False

> {-# LANGUAGE TypeOperators, UnicodeSyntax #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE ScopedTypeVariables #-}

> module AST where
> import           Control.Monad.Reader
> import qualified Data.Map.Strict as M
> import qualified Data.Set        as S
> import           Prelude hiding (lookup)


%endif


\section{Implementaci\'on de un SAT Solver}

\subsection{EDSL para la l\'ogica proposicional}

Primero definimos el \'arbol de sintaxis abstracta para la l\'ogica
proposicional. Utilizamos el mismo conjunto de conectivas que se
utiliza en las diapositivas del curso, agregando las constantes
$\top$ y $\bot$ por conveniencia.

> data Prop a =
>    Top
>   | Bot
>   | Prop a :→ Prop a
>   | Prop a :∧ Prop a
>   | Prop a :∨ Prop a
>   | Neg (Prop a)
>   | Var a

%if False

>   deriving (Eq, Show, Read)

> infixr 8 :∧
> infixr 8 :∨
> infixr 7 :→

%endif

Se define un ambiente donde se mapean letras proposicionales a valores
de verdad. Un ambiente corresponde a una valuaci\'on.

> newtype Env a = Env { runEnv :: (M.Map a Bool)}

La funci\'on $eval$ computa el valor de verdad dada una proposici\'on y su
valuaci\'on.

> eval :: (Ord a) ⇒ Prop a → Reader (Env a) Bool
> eval Top = return True
> eval Bot = return False
> eval (a :→ b) = eval a >>= \aval →
>                 if not aval
>                 then return True
>                 else eval b 
> eval (a :∧ b) = eval a >>= \aval →
>                 if not aval
>                 then return False
>                 else eval b
> eval (a :∨ b) = eval a >>= \aval →
>                 if aval
>                 then return True
>                 else eval b
> eval (Neg a) = not <$> eval a
> eval (Var p) = ask >>= \r →
>                case M.lookup p (runEnv r) of
>                  Just rval → return rval
>                  Nothing   → error "variable not in scope"


Dada una fórmula, la funci\'on $getLits$ recolecta sus letras proposicionales,
los ambientes de una f\'ormula a la hora de evaluarla deber\'ian tener como
dominio \'este conjunto de literales.

> getLetts :: (Ord a) ⇒ Prop a → S.Set a
> getLetts Top      = S.empty
> getLetts Bot      = S.empty
> getLetts (a :∧ b) = getLetts a `S.union` getLetts b
> getLetts (a :∨ b) = getLetts a `S.union` getLetts b
> getLetts (a :→ b) = getLetts a `S.union` getLetts b
> getLetts (Neg a)  = getLetts a
> getLetts (Var a)  = S.singleton a

> isLit ∷ Prop a → Bool
> isLit (Var a)       = True
> isLit (Neg (Var a)) = True
> isLit _             = False

> nnf ∷ Prop a → Prop a
> nnf Top = Top
> nnf Bot = Bot
> nnf (Var a)  = Var a
> nnf (α :→ β) = nnf α :→ nnf β
> nnf (α :∧ β) = nnf α :∧ nnf β
> nnf (α :∨ β) = nnf α :∨ nnf β

> nnf (Neg (Neg α))  = nnf α
> nnf (Neg (α :→ β)) = nnf α :∨ nnf (Neg β)
> nnf (Neg (α :∧ β)) = nnf (Neg α) :∨ nnf (Neg β)
> nnf (Neg (α :∨ β)) = nnf (Neg α) :∧ nnf (Neg β)
> nnf (Neg Top) = Bot
> nnf (Neg Bot) = Top
> nnf (Neg (Var a)) = Neg (Var a) 


-- > class Show₁ ns a where
-- >   show₁ ∷ Proxy ns → a → String

-- > data Proxy a = Proxy

-- > instance (a ~ String) ⇒ Show₁ 'True (Prop a) where
-- >   show₁ p Top      = "Τ" 
-- >   show₁ p Bot      = "⊥"
-- >   show₁ p (α :∧ β) = "(" ++ show₁ p α ++ " ∧ " ++ show₁ p β ++ ")"
-- >   show₁ p (α :∨ β) = "(" ++ show₁ p α ++ " ∨ " ++ show₁ p β ++ ")"
-- >   show₁ p (α :→ β) = "(" ++ show₁ p α ++ " → " ++ show₁ p β ++ ")"
-- >   show₁ p (Neg α)  = "¬" ++ show₁ p α 
-- >   show₁ p (Var a)  = a

-- > instance (Show a) ⇒ Show₁ 'False (Prop a) where
-- >   show₁ p Top      = "Τ" 
-- >   show₁ p Bot      = "⊥"
-- >   show₁ p (α :∧ β) = "(" ++ show₁ p α ++ " ∧ " ++ show₁ p β ++ ")"
-- >   show₁ p (α :∨ β) = "(" ++ show₁ p α ++ " ∨ " ++ show₁ p β ++ ")"
-- >   show₁ p (α :→ β) = "(" ++ show₁ p α ++ " → " ++ show₁ p β ++ ")"
-- >   show₁ p (Neg α)  = "¬" ++ show₁ p α 
-- >   show₁ p (Var a)  = show a

-- > type family IsString a = r where
-- >   IsString [Char] = 'True
-- >   IsString a      = 'False

-- > instance (Show₁ ns a, IsString a ~ ns) ⇒ Show a where
-- >   show (a∷a) = show₁ (Proxy ∷ Proxy ns) (a ∷ a) ∷ String


> subFormulas ∷ Prop a → (Prop a, Prop a)
> subFormulas (a :∧ b) = (a,b)
> subFormulas (a :∨ b) = (a,b)
> subFormulas (a :→ b) = (a,b)

> isAnd ∷ Prop a → Bool
> isAnd (_ :∧_ ) = True
> isAnd _ = False

> f = ((((Var 4 :∧ (((Var (-9) :∨ ((((Var 3 :→ Var 13) :∨ Var 6 :→ Var (-8) :∧ Var 11) :∨ (((Var (-15) :→ Var 5) :→ Var 5 :∨ Var (-1)) :∧ ((Var (-3) :∨ Var 1) :∧ (Var 15 :→ Var (-12))))) :∨ (((Var (-13) :∨ Var 3) :∧ ((Var 14 :→ Var 15) :→ Var 6 :∨ Var (-7))) :∧ (Var (-2) :→ (Var 5 :∨ Var (-14) :→ Var (-2) :∧ Var (-11)))))) :∧ (Var (-3) :∧ (Var 5 :∧ Var 14))) :∧ (((Var 8 :→ ((Var (-13) :∧ Var 1 :→ Var (-6) :∧ Var 9) :→ Var (-8))) :∧ Var 2) :∨ Var (-5) :→ Var (-7)))) :∧ Var (-2)) :∨ (Var (-3) :→ ((((((Var (-13) :∧ Var 14) :∧ (Var 8 :∨ Var (-5))) :∧ Var (-12)) :∨ (Var (-11) :∨ (Var (-2) :∧ Var (-11) :→ (Var 11 :→ Var (-5)))) :→ (((Var (-7) :∨ Var (-11)) :∧ (Var (-9) :→ Var (-6))) :∨ ((Var (-14) :∨ Var 3) :∧ (Var 7 :∧ Var (-6)))) :∨ Var (-3)) :∧ (Var 13 :∨ Var 10) :→ Var (-12) :∧ (((Var 12 :→ (Var 5 :∧ Var (-6)) :∨ (Var (-3) :→ Var (-15))) :∨ (((Var (-8) :→ Var (-2)) :∧ (Var (-3) :∧ Var 4)) :∧ ((Var 4 :→ Var 8) :∧ Var (-13)))) :∨ ((((Var (-6) :∧ Var 11) :∧ Var 15) :∧ ((Var 6 :→ Var (-4)) :→ Var (-1) :∧ Var 7)) :∨ (Var 9 :∨ ((Var 10 :→ Var (-15)) :∧ (Var 11 :∨ Var 9)))))) :∧ ((((Var 4 :→ (Var (-9) :→ Var (-10)) :∨ (Var (-2) :∨ Var (-15))) :∧ ((Var 13 :→ (Var (-6) :→ Var (-7))) :∧ Var 9)) :∨ ((Var (-9) :∨ Var 7 :→ (Var (-1) :→ Var (-3)) :∨ (Var (-1) :∧ Var (-3))) :→ (Var (-11) :∧ (Var 5 :→ Var (-10)) :→ (Var 2 :∧ Var (-13)) :∨ (Var 0 :∨ Var (-12)))) :→ ((((Var (-5) :∧ Var (-7)) :∨ (Var (-6) :→ Var 1)) :∧ ((Var 5 :∨ Var 9) :∧ (Var 7 :→ Var 5))) :∨ (((Var 9 :→ Var (-2)) :∨ Var 10) :∨ (Var (-4) :∨ Var 15 :→ Var 3))) :∧ (((Var 13 :∨ Var (-9) :→ Var (-12)) :∨ ((Var (-11) :→ Var 4) :→ Var (-8))) :∨ Var 6)) :∧ (Var (-2) :→ (((Var 6 :∧ Var (-8)) :∧ (Var (-7) :→ Var 11) :→ (Var 10 :∨ Var 3) :∧ (Var 4 :∨ Var (-10))) :→ Var 4 :∨ ((Var 13 :∧ Var 11) :∧ Var 5)) :∨ ((Var 4 :→ (Var 11 :→ Var (-12)) :∧ Var 15) :∨ (((Var (-8) :→ Var 3) :→ (Var (-10) :→ Var (-1))) :∨ Var 7))))) :∨ ((Var (-11) :→ (Var 8 :∨ (((Var 13 :→ Var (-15)) :∧ (Var 6 :∨ Var 5)) :∨ ((Var (-1) :∨ Var (-14)) :∧ Var 15))) :∨ (Var 7 :∨ ((Var 6 :∧ Var (-8) :→ Var (-15) :∧ Var 1) :∧ ((Var 10 :∧ Var (-1)) :∨ Var (-11))))) :∧ ((((Var 0 :∧ Var 11) :∨ (((Var 4 :→ Var 5) :∧ Var (-12)) :∨ ((Var 11 :∧ Var (-3)) :∧ (Var 8 :→ Var 7)))) :∨ ((Var (-11) :∧ (Var (-4) :→ Var 13)) :∨ Var (-9) :→ Var 9)) :∧ Var (-14)) :→ Var 13))) :∧ ((Var (-12) :∧ (((Var 4 :→ (Var 3 :∧ ((Var (-15) :∨ Var (-3)) :∧ (Var 14 :∨ Var 4) :→ (Var 11 :→ Var (-4)) :∧ (Var (-7) :∧ Var (-13)))) :∨ (Var (-4) :→ Var 12 :∧ (Var 3 :∧ Var 7 :→ Var (-12)))) :∧ ((((Var 11 :→ Var 11) :∨ (Var (-7) :→ Var 7) :→ (Var (-13) :∧ Var (-12)) :∧ (Var 7 :∨ Var 14)) :∧ ((Var 13 :→ (Var (-13) :→ Var 8)) :∨ ((Var (-4) :∧ Var 12) :∨ (Var 5 :∧ Var (-12)))) :→ (((Var (-11) :∨ Var (-14)) :∧ Var 13) :∧ (Var (-14) :∧ (Var (-7) :∧ Var (-2)))) :∨ Var (-11)) :∧ ((Var (-14) :∧ (Var (-2) :→ Var 7) :→ Var 3 :∨ (Var 7 :→ Var (-5) :∨ Var (-2))) :∨ (((Var (-14) :→ Var 6) :∨ (Var (-12) :→ Var 8) :→ Var 7 :∨ (Var 1 :∧ Var (-5))) :∧ (((Var (-1) :∧ Var 14) :∧ (Var 14 :→ Var (-7))) :∧ Var 2))))) :∨ (((Var 2 :∧ Var (-2)) :∨ ((((Var (-4) :∧ Var 15) :∨ (Var (-14) :→ (Var (-4) :→ Var (-4)))) :∨ (Var 4 :∧ Var 14)) :∧ Var 2)) :∨ Var (-1)) :→ Var 6 :∧ Var 3)) :∧ (((((Var 5 :∧ (Var 1 :∨ ((Var 3 :→ (Var 10 :→ (Var (-14) :→ Var 1))) :→ Var (-5)))) :∧ ((((Var 6 :→ Var 15) :∧ (Var (-8) :→ Var (-15)) :→ (Var 10 :→ Var (-5) :∧ Var (-1))) :→ (Var (-1) :∧ Var 4 :→ Var 9 :∨ Var 9) :∨ ((Var (-13) :∨ Var 8) :∨ (Var (-5) :∧ Var (-5)))) :∨ (((Var (-9) :∧ (Var (-7) :∧ Var (-5))) :∧ (Var 5 :∧ Var 2)) :∨ Var 5) :→ ((Var (-14) :∧ (Var (-14) :∧ Var (-10)) :→ Var (-14)) :∧ (Var 9 :∨ (Var (-15) :∨ (Var (-7) :→ Var (-5))))) :∧ ((((Var (-13) :→ Var (-12)) :→ (Var (-3) :→ Var 1)) :→ Var (-14)) :→ (Var (-1) :→ (Var 8 :∧ Var 12) :∧ (Var 6 :→ Var 8))))) :∨ (Var 3 :∨ Var (-14))) :∧ (Var 4 :∧ ((Var 10 :∨ (((Var 3 :∧ (Var 9 :∨ Var (-6))) :∨ ((Var (-4) :∧ Var (-12)) :∨ (Var 0 :∨ Var 15))) :∧ (Var (-11) :∨ (Var 5 :→ (Var 2 :→ Var 6)))) :→ Var (-6) :∧ (((Var (-12) :→ Var 0) :∧ (Var (-5) :∨ Var (-4) :→ Var (-13) :∧ Var 12)) :∨ ((Var (-9) :→ Var 1) :∧ Var 8 :→ Var 11 :∨ Var 15))) :→ (Var (-14) :→ (((Var 5 :→ Var 8) :→ Var 15 :∧ Var 2) :∨ (Var (-5) :∨ (Var (-15) :∧ Var (-5))) :→ (Var (-10) :→ (Var 0 :∨ Var (-4)) :∧ (Var (-13) :∨ Var (-7))))) :∧ (Var (-4) :→ (Var (-12) :→ Var (-7)) :∨ ((Var (-10) :∧ (Var (-5) :∨ Var 1)) :∨ ((Var (-9) :→ Var (-5)) :∨ (Var (-15) :∧ Var (-13)))))))) :∨ ((((((((Var (-13) :∧ Var (-8)) :∧ (Var 14 :→ Var 4)) :∨ ((Var (-14) :→ Var 2) :∧ (Var 4 :→ Var (-4)))) :∨ ((Var 7 :∨ Var 3 :→ (Var (-4) :→ Var (-10))) :∧ Var 13)) :∨ ((Var 15 :→ Var 2 :∧ (Var (-15) :→ Var (-8))) :∧ ((Var 15 :∧ Var 10) :∨ Var 6 :→ Var (-15)))) :∨ Var (-4)) :∨ Var (-2)) :∧ ((Var 11 :∨ Var (-2)) :∨ Var (-6)) :→ Var 15)))) :∧ (((Var (-1) :∨ Var (-12)) :∧ (Var 3 :∨ Var 6 :→ (Var (-4) :→ (Var 4 :→ (Var 3 :∨ ((Var 14 :∧ Var (-4)) :∨ Var 12) :→ (Var 10 :→ (Var 11 :∧ Var 12) :∧ Var (-11)))) :∧ Var (-5)) :∧ Var (-15))) :∧ ((Var 5 :∨ Var (-3)) :∨ Var 10) :→ Var (-1))
