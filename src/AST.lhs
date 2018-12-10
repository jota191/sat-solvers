

%if False

> {-# LANGUAGE TypeOperators, UnicodeSyntax #-}
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

>   deriving (Eq,Show)

> infixr 8 :∧
> infixr 8 :∨
> infixr 7 :→

%endif

Se define un ambiente donde se mapean letras proposicionales a valores
de verdad. Un ambiente corresponde a una valuaci\'on.

> newtype Env a = Env { runEnv :: (M.Map a Bool)} deriving Show

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

> getLits :: (Ord a) ⇒ Prop a → S.Set a
> getLits Top      = S.empty
> getLits Bot      = S.empty
> getLits (a :∧ b) = getLits a `S.union` getLits b
> getLits (a :∨ b) = getLits a `S.union` getLits b
> getLits (a :→ b) = getLits a `S.union` getLits b
> getLits (Neg a)  = getLits a
> getLits (Var a)  = S.singleton a
