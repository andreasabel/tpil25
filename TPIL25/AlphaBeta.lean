-- Prove correctness of alpha-beta pruning in the minimax alpha-beta algorithm.

import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.BoundedOrder.Basic

-- TODO: Organize parameters into a class.

namespace AlphaBeta
-- Parameters of the algorithm.

-- We model the game as a finitely-branching tree
-- with nodes given by a type of positions and
-- subtrees given by a function `children` that returns a list of nodes.
-- Leafs are simply nodes with no children.
variable
  {Position : Type}
  (children : Position → List Position)

-- We valuate positions in a total bounded order with involution.
variable
  {Value : Type}
  [order : LinearOrder Value]
  [bounded : BoundedOrder Value]
  (value : Position → Value)

-- We have two players, `Max` and `Min`, that alternate turns.

inductive Player : Type
  | Max
  | Min

def Player.other : Player → Player
  | Player.Max => Player.Min
  | Player.Min => Player.Max

-- Maximize the value of the position for `Max` and minimize it for `Min`.

def Player.max (turn : Player) : (a b : Value) -> Value :=
  match turn with
    | Player.Max => order.max
    | Player.Min => order.min

def Player.bot (turn : Player) : Value :=
  match turn with
    | Player.Max => bounded.bot
    | Player.Min => bounded.top

#check max

def Player.maximum (turn : Player) : List Value → Value :=
  List.foldl (max turn) (bot turn)

-- function minimax(node, depth, maximizingPlayer) is
--     if depth = 0 or node is a terminal node then
--         return the heuristic value of node
--     if maximizingPlayer then
--         value := −∞
--         for each child of node do
--             value := max(value, minimax(child, depth − 1, FALSE))
--         return value
--     else (* minimizing player *)
--         value := +∞
--         for each child of node do
--             value := min(value, minimax(child, depth − 1, TRUE))
--         return value

def Player.minimax (player : Player) (depth : Nat) (root : Position) : Value :=
  match depth with
    | 0 => value root
    | depth + 1 =>
        player.maximum $ List.map (player.other.minimax depth) $ children root

-- Intervals of values for alpha-beta pruning.

structure Interval (Value : Type) where
  alpha : Value
  beta  : Value

#check Interval

-- TODO: How to get rid of (Value := Value)?

def Interval.full : Interval (Value := Value) :=
  { alpha := bounded.bot, beta := bounded.top }

def Interval.contains (interval : Interval (Value := Value)) (value : Value) : Bool :=
  interval.alpha <= value && value <= interval.beta

def Player.update (turn : Player) (value : Value) : Interval (Value := Value) → Interval (Value := Value)
  | { alpha, beta } =>
    match turn with
      | Player.Max => { alpha := order.max alpha value, beta }
      | Player.Min => { alpha, beta := order.min beta value }

def Player.beyond (turn : Player) (interval : Interval (Value := Value)) (value : Value) : Bool :=
  match turn with
    | Player.Max => interval.beta <= value
    | Player.Min => value <= interval.alpha

-- Soft fail variant of alpha-beta pruning.
--
-- function alphabeta(node, depth, α, β, maximizingPlayer) is
--     if depth == 0 or node is terminal then
--         return the heuristic value of node
--     if maximizingPlayer then
--         value := −∞
--         for each child of node do
--             value := max(value, alphabeta(child, depth − 1, α, β, FALSE))
--             α := max(α, value)
--             if value ≥ β then
--                 break (* β cutoff *)
--         return value
--     else
--         value := +∞
--         for each child of node do
--             value := min(value, alphabeta(child, depth − 1, α, β, TRUE))
--             β := min(β, value)
--             if value ≤ α then
--                 break (* α cutoff *)
--         return value


mutual

  def Player.alphabeta (player : Player) (depth : Nat) (interval : Interval (Value := Value)) (root : Position): Value :=
    match depth with
      | 0 => value root
      | depth + 1 => player.alphabetas depth interval player.bot $ children root


  def Player.alphabetas (player : Player) (depth : Nat) (interval : Interval (Value := Value)) (value : Value) (nodes : List Position): Value :=
    match nodes with
      | [] => value
      | node :: nodes =>
        -- soft fail
        if player.beyond interval value then
          value
        else
          let value' := player.max value $ player.other.alphabeta depth interval node
          let interval' := player.update value' interval
          player.alphabetas depth interval' value' nodes

end

-- Correctness of alpha-beta pruning.
-- Theorem: `alphabeta` on the full interval returns the same value as `minimax`.

theorem alphabeta_correctness (player: Player) (depth : Nat) (root : Position) :
  player.alphabeta (depth := depth) (interval := Interval.full) (root := root) =
  player.minimax (depth := depth) (root := root) :=
  sorry

end AlphaBeta
