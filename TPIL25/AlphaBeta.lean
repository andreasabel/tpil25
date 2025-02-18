-- Prove correctness of alpha-beta pruning in the minimax alpha-beta algorithm.

import Mathlib.Tactic.Basic
import Mathlib.Tactic.LiftLets

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

#print flip
instance DecidablePlayerLe (turn : Player) : DecidableRel (Player.le (Value := Value) turn) :=
  match turn with
    | Player.Max => order.decidableLE
    -- -- | Player.Min => flip order.decidableLE -- error
    | Player.Min => fun a b => order.decidableLE b a


def Player.le_refl : (turn : Player) -> Reflexive (turn.le (Value := Value))
  | Player.Max => order.le_refl
  | Player.Min => order.le_refl

def Player.le_trans : (turn : Player) -> Transitive (turn.le (Value := Value))
  | Player.Max => order.le_trans
  | Player.Min => fun a b c h1 h2 => order.le_trans c b a h2 h1

def Player.le_other (turn : Player) (a b : Value) : turn.other.le a b → turn.le b a :=
  match turn with
    | Player.Max => id
    | Player.Min => id

def Player.other_le (turn : Player) (a b : Value) : turn.le a b → turn.other.le b a :=
  match turn with
    | Player.Max => id
    | Player.Min => id

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

def Player.minimax_spec (player : Player) (depth : Nat) (root : Position) : Value :=
  match depth with
    | 0 => tree.rating root
    | depth + 1 =>
        player.maximum1 (tree.rating root) $
          List.map (player.other.minimax_spec depth) $ tree.children root

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

-- Generic version with switchable pruning.

mutual

  def Player.search (prune : Bool) (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (root : Position) : Value :=
    match depth with
      | 0 => tree.rating root
      | depth + 1 => player.searchs prune depth interval player.bot $ tree.children root

  -- Assume that `value` is not beyond the interval.
  def Player.searchs (prune : Bool) (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (value : Value) (nodes : List Position) : Value :=
    match nodes with
      | [] => value
      | node :: nodes =>
        let value1 := player.other.search prune depth interval node
        if player.le value1 value then
          player.searchs prune depth interval value nodes
        else if prune && player.beyond interval value1 then
          value1
        else
          player.searchs prune depth (player.update value1 interval) value1 nodes

end

-- Theorem: If pruning is disabled, the interval does not matter.

mutual
  theorem Player.search_no_prune (player : Player) (depth : Nat) (interval1 interval2 : Interval (Value := Value)) (root : Position) :
    player.search false depth interval1 root = player.search false depth interval2 root :=
    match depth with
      | 0 => by
          unfold Player.search
          rfl
      | depth + 1 => by
          unfold Player.search
          apply player.searchs_no_prune depth interval1 interval2 player.bot (tree.children root)

  theorem Player.searchs_no_prune (player : Player) (depth : Nat)
    (interval1 interval2 : Interval (Value := Value)) (value : Value) (nodes : List Position) :
    player.searchs false depth interval1 value nodes =
    player.searchs false depth interval2 value nodes :=
    match nodes with
      | [] => by
          unfold Player.searchs
          rfl
      | node :: nodes => by
          unfold Player.searchs
          lift_lets
          intro value1 value1'
          have ih1: value1 = value1' := by
            apply player.other.search_no_prune
          simp [*]
          if h : player.le value1' value then
            simp [*]
            exact player.searchs_no_prune depth interval1 interval2 value nodes
          else
            simp [*]
            apply player.searchs_no_prune depth _ _ value1' nodes
end


-- Minimax.

def Player.minimax (player : Player) (depth : Nat)
    (root : Position) : Value :=
    player.search false depth Interval.full root

def Player.minimaxs (player : Player) (depth : Nat)
    (value : Value) (nodes : List Position) : Value :=
    player.searchs false depth Interval.full value nodes

-- Theorem: If pruning is disabled, `search` is equivalent to `minimax`.

theorem Player.search_minimax (player : Player) (depth : Nat) (interval : Interval (Value := Value)) (root : Position) :
    player.search false depth interval root = player.minimax depth root := by
    unfold minimax
    apply player.search_no_prune

-- Theorem: If pruning is disabled, `searchs` is equivalent to `minimaxs`.

theorem Player.search_minimaxs (player : Player) (depth : Nat) (interval : Interval (Value := Value)) (value : Value) (nodes : List Position) :
    player.searchs false depth interval value nodes = player.minimaxs depth value nodes := by
    unfold minimaxs
    apply player.searchs_no_prune


-- Alpha-beta pruning.

-- def Player.alphabeta := Player.search true -- type class problem

def Player.alphabeta (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (root : Position) : Value :=
    player.search true depth interval root

def Player.alphabetas (player : Player) (depth : Nat) (interval : Interval (Value := Value))
    (value : Value) (nodes : List Position) : Value :=
    player.searchs true depth interval value nodes

-- Correctness of alpha-beta pruning.

mutual

  theorem Player.alphabeta_correctness (player: Player) (depth : Nat)
    (interval : Interval (Value := Value)) (root : Position) :

    let vab := player.alphabeta depth interval root
    let vmm := player.minimax depth root
    -- If the minimax value is on one side of the interval,
    -- the alpha-beta value is on the same side.
    if player.le vmm interval.alpha then
      player.le vab interval.alpha
    else if player.le interval.beta vmm then
      player.le interval.beta vab
    -- Otherwise, if the minimax value is inside the interval,
    -- the alpha-beta value is the same as the minimax value.
    else vab = vmm :=
    
    by
      match depth with
      | 0 =>
        unfold Player.alphabeta
        unfold Player.minimax
        unfold Player.search
        simp [*]
        done
      | depth + 1 =>
        let nodes := tree.children root
        unfold Player.alphabeta
        unfold Player.minimax
        unfold Player.search
        intro vab vmm

        split
        case isTrue => -- player.le vmm interval.alpha =>
          have ih := player.alphabetas_correctness depth interval player.bot nodes
          unfold Player.alphabetas at ih
          unfold Player.minimaxs at ih
          simp [*] at ih
          exact ih
          done
        case isFalse =>
          split
          case isTrue =>
            have ih := player.alphabetas_correctness depth interval player.bot nodes
            unfold Player.alphabetas at ih
            unfold Player.minimaxs at ih
            simp [*] at ih
            exact ih
            done
          case isFalse =>
            have ih := player.alphabetas_correctness depth interval player.bot nodes
            unfold Player.alphabetas at ih
            unfold Player.minimaxs at ih
            simp [*] at ih
            exact ih
            done
          done



        done
        split

        lift_lets

        cases
        unfold Player.alphabeta
        unfold Player.minimax
        simp [0]
        done



  theorem Player.alphabetas_correctness (player: Player) (depth : Nat)
    (interval : Interval (Value := Value)) (value : Value) (nodes : List Position) :

    let vab := player.alphabetas depth interval value nodes
    let vmm := player.minimaxs depth value nodes
    -- If the minimax value is on one side of the interval,
    -- the alpha-beta value is on the same side.
    if player.le vmm interval.alpha then
      player.le vab interval.alpha
    else if player.le interval.beta vmm then
      player.le interval.beta vab
    -- Otherwise, if the minimax value is inside the interval,
    -- the alpha-beta value is the same as the minimax value.
    else
      vab = vmm := by
      sorry

end

-- Lemma: if we relax the interval, the value does not decrease.

mutual
  lemma relax_alphabeta (player : Player) (depth : Nat)
    (interval interval' : Interval (Value := Value))
    (sub : Interval.subset interval interval')
    (root : Position) :
    player.le (player.alphabeta (depth := depth) (interval := interval) (root := root))
              (player.alphabeta (depth := depth) (interval := interval') (root := root))
    := by
    cases depth -- generalizing interval interval' root
    case zero =>
      unfold Player.alphabeta
      apply player.le_refl
      done
    case succ depth =>
      unfold Player.alphabeta
      apply relax_alphabetas
      exact sub
      done

  lemma relax_alphabetas (player : Player) (depth : Nat)
    (interval  interval' : Interval (Value := Value))
    (sub : Interval.subset interval interval')
    (value : Value)
    (nodes : List Position) :
    player.le (player.alphabetas (depth := depth) (interval := interval) (value := value) (nodes := nodes))
              (player.alphabetas (depth := depth) (interval := interval') (value := value) (nodes := nodes))
    := by
    cases nodes
    case nil =>
      unfold Player.alphabetas
      apply player.le_refl
      done
    case cons node nodes =>
      unfold Player.alphabetas
      lift_lets
      intro value1 value1'
      -- let value1  := player.other.alphabeta depth interval node
      -- let value1' := player.other.alphabeta depth interval' node
      have ih1 : player.other.le value1 value1' := relax_alphabeta player.other depth interval interval' sub node
      -- let h := player.le value1 value

      if h : player.le value1 value then
        have h' : player.le value1' value := by
          sorry
          done
        simp [*]
        exact relax_alphabetas player depth interval interval' sub value nodes
        done
      else
        -- here I have value ≤ value1 and value1' ≤ value1
        -- which does not tell me how value1' compares to value
        -- so I do not know how to simplify the `if`.
        if b' : player.beyond interval' value1' then
        have b : player.beyond interval value1 := by
          sorry
          done
        simp [*]
        exact relax_alphabetas player depth interval interval' sub value node nodes
        done
      else
        exact relax_alphabetas player depth (player.update value1 interval) interval' sub value1 nodes
        done
      done

    --   cases player.le value1 value with
    --   | true =>
    --     apply relax_alphabetas
    --     exact sub
    --     done
    --   match (player.le value1 value) with
    --   | true =>
    --     apply relax_alphabetas
    --     exact sub
    --     done

    --   cases player with
    --   | Max =>
    --     unfold Player.alphabetas
    --     apply relax_alphabetas
    --     exact sub
    --     done
    --   | Min =>
    --     unfold Player.alphabetas
    --     exact relax_alphabetas Player.Min depth interval interval' sub value node nodes
    --     done
    --   done
    -- done

end

#check Player.alphabetas

-- Correctness of alpha-beta pruning.
-- Theorem: `alphabeta` on the full interval returns the same value as `minimax`.

theorem alphabeta_correctness (player: Player) (depth : Nat) (root : Position) :
  player.alphabeta (depth := depth) (interval := Interval.full) (root := root) =
  player.minimax (Value := Value) (depth := depth) (root := root) :=
  sorry

end AlphaBeta
