%if False

> {-# LANGUAGE TypeOperators, UnicodeSyntax #-}

> module Main where
> import AST
> import           Control.Monad.Reader
> import qualified Data.Map.Strict as M
> import qualified Data.Set        as S
> import           Prelude hiding (lookup)
> import           Data.Char

%endif

\subsection{Iplementaci\'on mediante tablas de Verdad}

Dado un conjunto de literales, generamos la lista de todas las
posibles valuaciones con la función $genVals$

> genVals :: (Ord a) ⇒ S.Set a → [Env a]
> genVals lits = map (Env . M.fromList) $ sequence
>              $ map (\s -> [(s,True), (s,False)]) (S.toList lits)

TODO: optimizar esto

Finalmente la función $sat$ decide si la fórmula es satisfactible.

> sat :: (Ord a) ⇒ Prop a → Bool
> sat p = let lits = getLits p
>             vals = genVals lits
>         in  or $ map (runReader (eval p)) vals

Gracias a la evaluaci\'on perezosa la implementaci\'on tal y como está
consume espacio constante ($vals$ se va consumiendo a demanda). Además
$eval$ impl\'icitamente optimiza los cálculos en las conectivas.

%if False

> p = Var "p" ; q = Var "q" ; r = Var "r"
> s = Var "s" ; t = Var "t" ; u = Var "u"

> nonsat1 = Neg $ (p :∨ q :→ Neg p :→ q) :∧ ((Neg p :→ q) :→ p :∨ q)
> test2 = (p :∧ q :→ r) :→ s :∨ t :→ u


> f1 :: Int → Prop Char
> f1 n
>   = let p = Neg $ Var (chr (97+n))
>         q = Neg $ Var (chr (98+n))
>         r = Neg $ Var (chr (99+n))
>         s = Neg $ Var (chr (100+n))
>     in  p :∧ q :∧ r :∧ s

> f2 0 = f1 0
> f2 n = f1 n :→ f2 (n-1)

> f3 0 = f1 0
> f3 n = f3 (n-1) :∧ f1 n 



> main = (print . sat . f3) 16

%endif
