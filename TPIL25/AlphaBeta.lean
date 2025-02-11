-- Prove correctness of alpha-beta pruning in the minimax alpha-beta algorithm.

import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.BoundedOrder.Basic

-- TODO: Organize parameters into a class.

class Tree (Position : Type) (Value : Type) where
  children : Position → List Position
  rating : Position → Value

namespace AlphaBeta
-- Parameters of the algorithm.

-- We valuate positions in a linear bounded order.
variable
  {Value : Type}
  [order : LinearOrder Value]
  [bounded : BoundedOrder Value]

-- We model the game as a finitely-branching tree
-- with nodes given by a type of positions and
-- subtrees given by a function `children` that returns a list of nodes.
-- Leafs are simply nodes with no children.
variable
  {Position : Type}
  [tree : Tree Position Value]


-- We have two players, `Max` and `Min`, that alternate turns.

inductive Player : Type
  | Max
  | Min

def Player.other : Player → Player
  | Player.Max => Player.Min
  | Player.Min => Player.Max

def Player.le (turn : Player) : Value → Value → Prop :=
  match turn with
    | Player.Max => order.le
    | Player.Min => flip order.le

def Player.ge (turn : Player) : Value → Value → Prop :=
  match turn with
    | Player.Max => flip order.le
    | Player.Min => order.le

instance DecidablePlayerLe (turn : Player) : DecidableRel (Player.le (Value := Value) turn) :=
  match turn with
    | Player.Max => order.decidableLE
    | Player.Min => _


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

def Player.maximum1 (turn : Player) (base : Value) : List Value → Value :=
  List.foldl (max turn) base

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
    | 0 => tree.rating root
    | depth + 1 =>
        player.maximum1 (tree.rating root) $
          List.map (player.other.minimax depth) $ tree.children root

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

def Interval.subset (interval1 interval2 : Interval (Value := Value)) : Bool :=
  interval1.alpha >= interval2.alpha && interval1.beta <= interval2.beta

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


-- Version 0 of the algorithm with soft fail.

mutual

  def Player.alphabeta0 (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (root : Position) : Value :=
    match depth with
      | 0 => tree.rating root
      | depth + 1 => player.alphabetas0 depth interval player.bot $ tree.children root


  def Player.alphabetas0 (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (value : Value)
    (nodes : List Position) : Value :=
    match nodes with
      | [] => value
      | node :: nodes =>
        -- soft fail
        if player.beyond interval value then
          value
        else
          let value' := player.max value $ player.other.alphabeta0 depth interval node
          let interval' := player.update value' interval
          player.alphabetas0 depth interval' value' nodes

end

mutual

  def Player.alphabeta (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (root : Position) : Value :=
    match depth with
      | 0 => tree.rating root
      | depth + 1 => player.alphabetas depth interval player.bot $ tree.children root

  -- Assume that `value` is not beyond the interval.
  def Player.alphabetas (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (value : Value) (nodes : List Position) : Value :=
    match nodes with
      | [] => value
      | node :: nodes =>
        let value1 := player.other.alphabeta depth interval node
        if player.le value1 value then
          player.alphabetas depth interval value nodes
        else if player.beyond interval value1 then
          value1
        else
          player.alphabetas depth (player.update value1 interval) value1 nodes

end

-- Lemma: if we relax the interval, the value does not decrease.

mutual
  lemma relax_alphabeta (player : Player) (depth : Nat)
    (interval  : Interval (Value := Value))
    (interval' : Interval (Value := Value))
    (sub : Interval.subset interval interval')
    (root : Position) :
    player.alphabeta (depth := depth) (interval := interval)  (root := root) ≤
    player.alphabeta (depth := depth) (interval := interval') (root := root)
    := by
    cases depth -- generalizing interval interval' root
    case zero =>
      unfold Player.alphabeta
      exact le_refl _
      done
    case succ depth =>
      unfold Player.alphabeta
      apply relax_alphabetas
      exact sub
      done

  lemma relax_alphabetas (player : Player) (depth : Nat)
    (interval  : Interval (Value := Value))
    (interval' : Interval (Value := Value))
    (sub : Interval.subset interval interval')
    (value : Value)
    (nodes : List Position) :
    player.alphabetas (depth := depth) (interval := interval)  (value := value) (nodes := nodes) ≤
    player.alphabetas (depth := depth) (interval := interval') (value := value) (nodes := nodes)
    := by
    cases nodes
    case nil =>
      unfold Player.alphabetas
      exact le_refl _
      done
    case cons node nodes =>
      unfold Player.alphabetas
      let value1  := player.other.alphabeta depth interval node
      let value1' := player.other.alphabeta depth interval' node
      have ih1 : value1 ≤ value1' := relax_alphabeta player.other depth interval interval' sub node
      -- let h := player.le value1 value

      if h' : player.le value1' value then
        have h : player.le value1 value := by
          
          done
        simp [*]
        exact relax_alphabetas player depth interval interval' sub value nodes
        done
      else if player.beyond interval value1 then
        exact relax_alphabetas player depth interval interval' sub value node nodes
        done
      else
        exact relax_alphabetas player depth (player.update value1 interval) interval' sub value1 nodes
        done
      done

      cases player.le value1 value with
      | true =>
        apply relax_alphabetas
        exact sub
        done
      match (player.le value1 value) with
      | true =>
        apply relax_alphabetas
        exact sub
        done

      cases player with
      | Max =>
        unfold Player.alphabetas
        apply relax_alphabetas
        exact sub
        done
      | Min =>
        unfold Player.alphabetas
        exact relax_alphabetas Player.Min depth interval interval' sub value node nodes
        done
      done
    done

end

#check Player.alphabetas

-- Correctness of alpha-beta pruning.
-- Theorem: `alphabeta` on the full interval returns the same value as `minimax`.

theorem alphabeta_correctness (player: Player) (depth : Nat) (root : Position) :
  player.alphabeta (depth := depth) (interval := Interval.full) (root := root) =
  player.minimax (Value := Value) (depth := depth) (root := root) :=
  sorry

end AlphaBeta
