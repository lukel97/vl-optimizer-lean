import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.MinMax

inductive DemandedVL
| vlmax
| vlconst (n : Nat)
deriving DecidableEq

instance : LE DemandedVL where
  le : DemandedVL → DemandedVL → Prop
  | _, .vlmax => true
  | .vlmax, .vlconst _ => false
  | .vlconst a, .vlconst b => a ≤ b

instance (a b : DemandedVL) : Decidable (a ≤ b) := by
  cases a with
  | vlmax => cases b <;> simp [LE.le] <;> infer_instance
  | vlconst x => cases b with
    | vlmax => simp [LE.le]; infer_instance
    | vlconst y => exact inferInstanceAs (Decidable (x ≤ y))

instance : Max DemandedVL := maxOfLe
instance : Min DemandedVL := minOfLe

namespace DemandedVL

instance : Preorder DemandedVL where
  le_refl (a : DemandedVL) : a ≤ a := by
    cases a
    · rfl
    · apply Nat.le_refl
  le_trans (a b c : DemandedVL) : a ≤ b → b ≤ c → a ≤ c := by
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp [instLEDemandedVL]; apply Nat.le_trans

instance : PartialOrder DemandedVL where
  le_antisymm (a b : DemandedVL) : a ≤ b → b ≤ a → a = b := by
    cases a <;> cases b <;> simp [instLEDemandedVL, antisymm_iff]; omega

protected theorem max_def {a b : DemandedVL} : max a b = if a ≤ b then b else a := rfl
protected theorem min_def {a b : DemandedVL} : min a b = if a ≤ b then a else b := rfl

instance : LinearOrder DemandedVL where
  le_total (a b : DemandedVL) : a ≤ b ∨ b ≤ a := by
    simp [instLEDemandedVL]
    cases a <;> cases b <;> simp; apply Nat.le_total
  toDecidableLE := inferInstance
  max_def := @DemandedVL.max_def
  min_def := @DemandedVL.min_def

@[simp]
theorem le_nat {a b : Nat} : (vlconst a ≤ vlconst b) = (a ≤ b) := by rfl

instance : SemilatticeSup DemandedVL where
  sup := max
  le_sup_left : ∀ a b : DemandedVL, a ≤ a ⊔ b := by simp
  le_sup_right : ∀ a b : DemandedVL, b ≤ a ⊔ b := by simp
  sup_le : ∀ a b c : DemandedVL, a ≤ c → b ≤ c → a ⊔ b ≤ c := by
    intro a b c hac hbc
    rcases max_choice a b with h | h <;> rw [h] <;> assumption

instance : Bot DemandedVL where
  bot := vlconst 0

instance : OrderBot DemandedVL where
  bot_le {a : DemandedVL} : ⊥ ≤ a := by
    cases a
    · rfl
    · simp [Bot.bot]

instance : Top DemandedVL where
  top := vlmax

instance : OrderTop DemandedVL where
  le_top {a : DemandedVL} : a ≤ ⊤ := by cases a <;> rfl

end DemandedVL

instance (l1 l2 : Option DemandedVL) : Decidable (l1 ≤ l2) := by
  cases l1 <;> cases l2 <;> simp <;> infer_instance

instance : Preorder (Option DemandedVL) where
  le_refl (a : Option DemandedVL) : a ≤ a := by cases a <;> simp
  le_trans (a b c : Option DemandedVL) : a ≤ b → b ≤ c → a ≤ c := by
    cases a <;> cases b <;> cases c <;> simp ; apply le_trans
  lt_iff_le_not_le (a b : Option DemandedVL) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
    cases a <;> cases b <;> simp ; apply le_of_lt

instance : PartialOrder (Option DemandedVL) where
  le_antisymm := by
    intro a b
    cases a <;> cases b <;> simp ; apply le_antisymm

instance : LinearOrder (Option DemandedVL) where
  le_total (a b : Option DemandedVL) : a ≤ b ∨ b ≤ a := by
    simp [instLEOption, instLEDemandedVL]
    cases a <;> cases b <;> simp [Option.le]
    rename_i v1 v2
    cases v1 <;> cases v2 <;> simp ; apply Nat.le_total
  toDecidableLE := inferInstance
  max_def (a b : Option DemandedVL) : max a b = if a ≤ b then b else a := by
    rcases a with rfl | a <;> rcases b with rfl | b <;> simp
    apply apply_ite some
  min_def (a b : Option DemandedVL) : min a b = if a ≤ b then a else b := by
    rcases a with rfl | a <;> rcases b with rfl | b <;> simp
    apply apply_ite some
  compare_eq_compareOfLessAndEq (a b : Option DemandedVL) := by
    rcases a with rfl | a <;> rcases b with rfl | b <;> simp [compare, compareOfLessAndEq]
    cases a <;> cases b <;> simp

instance : SemilatticeSup (Option DemandedVL) where
  sup := Option.max
  le_sup_left := le_max_left
  le_sup_right := le_max_right
  sup_le (_ _ _ : Option DemandedVL) := max_le

instance : SemilatticeInf (Option DemandedVL) where
  inf := Option.min
  inf_le_left := min_le_left
  inf_le_right := min_le_right
  le_inf (_ _ _ : Option DemandedVL) := le_min

instance : Lattice (Option DemandedVL) where

instance : Bot (Option DemandedVL) where
  bot := none

instance : OrderBot (Option DemandedVL) where
  bot_le := by
    intro a
    cases a <;> simp [instBotOptionDemandedVL]

instance : Top (Option DemandedVL) where
  top := some .vlmax

instance : OrderTop (Option DemandedVL) where
  le_top := by
    intro a
    cases a <;> simp [instTopOptionDemandedVL]
    exact le_top

/-- Instructions are represented by natural numbers. -/
abbrev Instr := Nat

/--
Our DemandedVL map is a map from instructions to DemandedVLs.

This is a function/'extensional' encoding.

Instructions might not be in the map, hence the Option.

Represents the DenseMap<const MachineInstr *, DemandedVL> in RISCVVLOptimizer.cpp
-/
abbrev Map := Instr -> Option DemandedVL

instance : Bot Map where
  bot := fun _ => none

instance : OrderBot Map where
  bot_le {a : Map} : ⊥ ≤ a := by
    intro v
    simp

instance : Top Map where
  top := fun _ => some .vlmax

instance : OrderTop Map where
  le_top {a : Map} : a ≤ ⊤ := by intro v; simp

/-- 
The join of two maps is the map created by joining each instruction's demanded VL.
-/
instance : Max (Map) where
  max a b := fun v => (a v) ⊔ (b v)

/--
A map is considered less than or equal another map iff each instruction's demanded VL is less than or equal.
-/
instance : LE Map where
  le (a b : Map) : Prop :=
    ∀ (v : Instr), a v ≤ b v

instance : Preorder Map where
  le_refl (a : Map) : a ≤ a := by intro i; rfl
  le_trans (a b c : Map) : a ≤ b → b ≤ c → a ≤ c := by
    intros hab hbc
    intros v
    specialize (hab v)
    specialize (hbc v)
    apply le_trans <;> assumption

instance : PartialOrder Map where
  le_antisymm (a b : Map) : a ≤ b → b ≤ a → a = b := by
    intros hab hba
    ext i vl
    simp [le_antisymm hab hba]

instance : SemilatticeSup Map where
  sup := max
  le_sup_left : ∀ a b : Map, a ≤ a ⊔ b := by
    intros
    intro
    simp [instMaxMap]
  le_sup_right : ∀ a b : Map, b ≤ a ⊔ b := by
    intros
    intro
    simp [instMaxMap]
  sup_le : ∀ a b c : Map, a ≤ c → b ≤ c → a ⊔ b ≤ c := by
    intros a b c hab hbc
    simp [instLEMap, instMaxMap]
    intro v
    exact ⟨hab v, hbc v⟩

def Map.insert (m : Map) (i : Instr) (x : Option DemandedVL) : Map :=
  fun j => if i = j then x else m j

theorem Map.insert_le_of_le {x y : Map} {vl1 vl2 : Option DemandedVL} {i : Instr}
  (hxy : x ≤ y) (hvl : vl1 ≤ vl2) : Map.insert x i vl1 ≤ Map.insert y i vl2 := by
  intro j
  unfold Map.insert
  by_cases heq : i = j
  · simp [heq]; assumption
  · simp [heq]; exact hxy j

opaque instr_vls : Instr → Option DemandedVL
opaque instr_ops : Instr -> List Instr

def transfer' (ops : List Instr) (i : Instr) (x : Map) : Map :=
  match ops with
  | (op :: rest) =>
        let prev := transfer' rest i x
        Map.insert prev op (max (prev op) (min (x i) (instr_vls op)))
  | [] => ⊥

def transfer (i : Instr) (x : Map) : Map :=
  transfer' (instr_ops i) i x

theorem transfer'_monotonic {ops : List Instr} {i : Instr} {x y : Map} (h : x ≤ y) :
  transfer' ops i x ≤ transfer' ops i y := by
  unfold transfer'
  cases ops
  · simp
  · simp
    apply Map.insert_le_of_le
    apply transfer'_monotonic h
    apply max_le_max
    apply transfer'_monotonic h
    apply min_le_min_right
    exact h i

theorem transfer_monotonic {i : Instr} {x y : Map}
    (hxy : x ≤ y) : (transfer i x) ≤ (transfer i y) := by
  unfold transfer
  apply transfer'_monotonic
  assumption
  
