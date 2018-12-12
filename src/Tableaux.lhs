%if False


> {-# LANGUAGE UnicodeSyntax #-}
> {-# LANGUAGE TypeOperators #-}

> module Main where

> import AST
> import           Data.Stack
> import qualified Data.Map.Strict as M
> import qualified Data.Set        as S

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
> initNode α = let toMap = M.fromList . S.toList
>                  lits  = (toMap . S.map (\a → (a, None)) . getLetts . nnf) α
>                  forms = stackPush stackNew α
>              in  Node lits forms 

La función $closed$ decide si una rama está cerrada, esto es, que
tenga una contradicción (la misma letra proposicional positiva y negativa)

> closed ∷ Node a → Bool
> closed (Node lits _) = elem Both $ M.elems lits

> leaf ∷ Node a → Bool
> leaf (Node _ forms) = stackIsEmpty forms

> wrap a = [a]
> pop  = stackPop
> push = stackPush

> compute ∷ (Ord a) ⇒ Node a → [Node a]
> compute node@(Node lits forms)
>   = case pop forms of
>       Nothing     → wrap node
>       Just (fs,f) →
>         case f of
>           (α :∧ β) → wrap $ Node lits $ push (push fs α) β
>           (α :∨ β) → [Node lits (push fs α),
>                       Node lits (push fs β)]
>           (α :→ β) → [Node lits (push fs (nnf (Neg α))),
>                       Node lits (push fs β)]
>           (Neg (Var a)) → case M.lookup a lits of
>                            Just None → [Node (M.insert a Nega lits) fs]
>                            Just Nega → [Node lits fs]
>                            Just Posi → []
>                            Just Both → []
>           (Var a) → case M.lookup a lits of
>                       Just None → [Node (M.insert a Posi lits) fs]
>                       Just Nega → []
>                       Just Posi → [Node lits fs]
>                       Just Both → []
>           Top → [Node lits fs]
>           Bot → []

> main = print "ok"

> p = Var "p" ; q = Var "q" ; r = Var "r"
> s = Var "s" ; t = Var "t" ; u = Var "u"

> nonsat1 = Neg $ (p :∨ q :→ Neg p :→ q) :∧ ((Neg p :→ q) :→ p :∨ q)
> test2 = (p :∧ q :→ r) :→ s :∨ t :→ u
