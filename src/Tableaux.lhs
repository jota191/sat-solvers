%if False


> {-# LANGUAGE UnicodeSyntax #-}
> {-# LANGUAGE TypeOperators #-}

> module Tableaux where

> import AST
> import           Data.Stack
> import qualified Data.Map.Strict as M
> import qualified Data.Set        as S
> import Control.Monad.Logic

%endif


Para implementar el tableaux, modelamos cada nodo posible del árbol de
la siguiente manera: 
Cada nodo tiene literales o sus negaciones, que ya no serán procesados;
además un conjunto de fórmulas más complejas que están pendientes de procesar.
Qué fórmula elegimos procesar introduce otro factor de no determinismo
que queremos eliminar, por lo que introducimos un órden:
utilizaremos un stack, procesando el tope e introduciendo las subfórmulas
cada vez.


> data LitState = None | Posi | Nega | Both deriving (Eq, Show, Ord)

> data Node a = Node { lits  :: M.Map a LitState,
>                      forms :: Stack (Prop a) } deriving Show

El tableaux comienza con la fórmula de entrada como único habitante de la pila,
y todos los literales en estado $None$.

> initNode :: (Ord a) ⇒ Prop a → Node a
> initNode α = let α'    = nnf α
>                  toMap = M.fromList . S.toList
>                  lits  = (toMap . S.map (\a → (a, None)) . getLetts) α'
>                  forms = stackPush stackNew α'
>              in  Node lits forms 

La función $closed$ decide si una rama está cerrada, esto es, que
tenga una contradicción (la misma letra proposicional positiva y negativa)
$compute$ no debería generar ramas cerradas..

> closed ∷ Node a → Bool
> closed (Node lits _) = elem Both $ M.elems lits

> leaf ∷ Node a → Bool
> leaf (Node _ forms) = stackIsEmpty forms

> msum' ∷ MonadPlus m ⇒ [a] → m a
> msum' = msum . map return

> pop  = stackPop
> push = stackPush

> branch ∷ (Ord a) ⇒ Node a → Logic (Node a)
> branch node@(Node lits forms)
>   = case pop forms of
>       Nothing     → return node
>       Just (fs,f) →
>         case f of
>           (α :∧ β) → return $ Node lits $ push (push fs α) β
>           (α :∨ β) → msum' [Node lits (push fs α),
>                             Node lits (push fs β)]
>           (α :→ β) → msum' [Node lits (push fs (nnf (Neg α)))
>                           , Node lits (push fs β)]
>           (Neg (Var a)) → case M.lookup a lits of
>                            Just None → return (Node(M.insert a Nega lits)fs)
>                            Just Nega → return (Node lits fs)
>                            Just Posi → mzero
>                            Just Both → mzero
>           (Var a) → case M.lookup a lits of
>                       Just None → return (Node (M.insert a Posi lits) fs)
>                       Just Nega → mzero
>                       Just Posi → return (Node lits fs)
>                       Just Both → mzero
>           Top → return (Node lits fs)
>           Bot → mzero

> tableaux ∷ (Ord a) ⇒ Node a → Logic (Node a)
> tableaux n
>   = branch n >>= \br → -- interleave is much less efficient, test this
>     if leaf br
>     then return br
>     else tableaux br

> sat ∷ (Ord a) ⇒ Prop a → Bool
> sat p = let root = initNode p
>         in  case observeMany 1 (tableaux root) of
>               [] → False
>               _  → True
