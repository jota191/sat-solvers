%if False


> {-# LANGUAGE UnicodeSyntax, TypeOperators #-}
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


> data LitState = None | Pos | Neg | Both deriving (Eq, Show, Ord)

> data Node a = Node { lits  :: M.Map a LitState,
>                      forms :: Stack (Prop a) } deriving Show

El tableaux comienza con la fórmula de entrada como único habitante de la pila,
y todos los literales en estado $None$.

> initNode :: (Ord a) ⇒ Prop a → Node a
> initNode α = let toMap = M.fromList . S.toList
>                  lits  = (toMap . S.map (\a → (a, None)) . getLetts) α
>                  forms = stackPush stackNew α
>              in  Node lits forms 

> main = print "ok"
