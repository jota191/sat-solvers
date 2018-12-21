%if False

> {-# LANGUAGE TypeOperators, UnicodeSyntax #-}

> module TruthTable where
> import AST
> import           Control.Monad.Reader
> import qualified Data.Map.Strict as M
> import qualified Data.Set        as S
> import           Prelude hiding (lookup)
> import           Data.Char

%endif

\subsection{Implementación mediante tablas de Verdad}

Dado un conjunto de literales, generamos la lista de todas las
posibles valuaciones con la función $genVals$

> genVals :: (Ord a) ⇒ S.Set a → [Env a]
> genVals lits = map (Env . M.fromList) $ sequence
>              $ map (\s -> [(s,True), (s,False)]) (S.toList lits)

TODO: optimizar esto

Finalmente la función $sat$ decide si la fórmula es satisfactible.

> sat :: (Ord a) ⇒ Prop a → Bool
> sat p = let lits = getLetts p
>             vals = genVals lits
>         in  or $ map (runReader (eval p)) vals

Gracias a la evaluaci\'on perezosa la implementaci\'on tal y como está
consume espacio constante ($vals$ se va consumiendo a demanda). Además
$eval$ impl\'icitamente optimiza los cálculos en las conectivas.
