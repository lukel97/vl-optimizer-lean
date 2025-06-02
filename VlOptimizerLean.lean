import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice

inductive DemandedVL
| vlmax
| vlconst (n : Nat)
deriving DecidableEq

instance : LE DemandedVL where
  le (l1 l2 : DemandedVL) : Prop :=
    match l1, l2 with
    | _, .vlmax => true
    | .vlmax, .vlconst _ => false
    | .vlconst a, .vlconst b => a <= b

instance (l1 l2 : DemandedVL) : Decidable (l1 ≤ l2) := by
  cases l1 with
  | vlmax => cases l2 <;> simp [LE.le] <;> infer_instance
  | vlconst n1 => cases l2 with
    | vlmax => simp [LE.le]; infer_instance
    | vlconst n2 => exact inferInstanceAs (Decidable (n1 ≤ n2))

instance : Max DemandedVL := maxOfLe
instance : Min DemandedVL := minOfLe

namespace DemandedVL

variable {a b c : DemandedVL}

/-- Le is reflexive -/
@[refl, simp]
theorem le_refl : a ≤ a := by cases a <;> simp [instLEDemandedVL]

/-- Le is antisymmetric -/
@[simp]
theorem le_antisymm_iff : a ≤ b ∧ b ≤ a ↔ (a = b) := by
  cases a <;> cases b <;> simp [instLEDemandedVL, antisymm_iff]

@[simp]
theorem le_antisymm : ∀ a b : DemandedVL, a ≤ b → b ≤ a → a = b := by
  intros a b; cases a <;> cases b <;> simp [instLEDemandedVL]; omega

/-- Le is transitive -/
@[simp]
theorem le_trans : a ≤ b → b ≤ c → a ≤ c := by
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp [instLEDemandedVL]; apply Nat.le_trans

instance : Preorder DemandedVL where
  le_refl (a : DemandedVL) : a ≤ a := DemandedVL.le_refl
  le_trans (a b c : DemandedVL) : a ≤ b → b ≤ c → a ≤ c := DemandedVL.le_trans

instance : PartialOrder DemandedVL where
  le_antisymm := DemandedVL.le_antisymm

protected theorem max_def {a b : DemandedVL} : max a b = if a ≤ b then b else a := rfl
protected theorem min_def {a b : DemandedVL} : min a b = if a ≤ b then a else b := rfl

instance : LinearOrder DemandedVL where
  le_total (a b : DemandedVL) : a ≤ b ∨ b ≤ a := by
    simp [instLEDemandedVL]
    cases a <;> cases b <;> simp; apply Nat.le_total
  toDecidableLE := inferInstance
  max_def := @DemandedVL.max_def
  min_def := @DemandedVL.min_def

theorem Nat.le_neq_symm {a b : ℕ} (hle : a ≤ b) (hne : a ≠ b) : ¬ b ≤ a := by
  apply not_le_of_lt
  exact lt_of_le_of_ne hle hne


theorem Nat.le_ite_congr {a b : ℕ} : (if a ≤ b then b else a) = (if b ≤ a then a else b) := by
  by_cases h : a = b
  · simp [h]
  · by_cases h2 : a ≤ b
    · simp [h2, Nat.le_neq_symm h2 h]
    · simp [h2, Nat.le_of_not_ge h2]

@[simp]
theorem max_comm {l1 l2 : DemandedVL} : l1 ⊔ l2 = l2 ⊔ l1 := by
  rcases l1 with _ | x <;> rcases l2 with _ | y <;> simp [DemandedVL.max_def, instLEDemandedVL]
  have h := le_or_gt x y
  match h with
  | Or.inl h =>
    simp [h]
    by_cases h2 : x = y
    · simp [h2]
    · simp [Nat.le_neq_symm h h2]
  | Or.inr h =>
    simp [Nat.not_le_of_gt h]
    by_cases h2 : x = y
    · simp [h2]
    · have h3 : y ≤ x := by omega
      simp [h3]

@[simp]
theorem max_idem {l : DemandedVL} : l ⊔ l = l := by
 rcases l with rfl | l <;> simp [DemandedVL.max_def]

theorem max_either {l1 l2 : DemandedVL} : l1 ⊔ l2 = l1 ∨ l1 ⊔ l2 = l2 := by
  cases l1 <;> cases l2 <;> simp only [DemandedVL.max_def] <;> rw [Or.comm] <;> apply ite_eq_or_eq

@[simp]
theorem le?_vlmax (l : DemandedVL) : l ≤ .vlmax := by
  rcases l with rfl | l <;> simp [LE.le]

@[simp]
theorem le_self_max (l1 l2 : DemandedVL) : l1 ≤ (l1 ⊔ l2) := by
  simp [DemandedVL.max_def]
  by_cases h : l1 ≤ l2 <;> simp [h]

@[simp]
theorem le_max_self (l1 l2 : DemandedVL) : l1 ≤ (l2 ⊔ l1) := by
  rw [max_comm]
  apply le_self_max

@[simp]
theorem le_nat {a b : Nat} : (vlconst a ≤ vlconst b) = (a ≤ b) := by rfl

@[simp]
theorem neq_le_not_le : a ≤ b → a ≠ b → ¬ b ≤ a := by
  cases a <;> cases b <;> simp [instLEDemandedVL]; omega

@[simp]
theorem vlmax_le : vlmax ≤ a ↔ a = vlmax := by
  cases a <;> simp [instLEDemandedVL]


end DemandedVL

instance : SemilatticeSup DemandedVL where
  sup := max
  le_sup_left : ∀ a b : DemandedVL, a ≤ a ⊔ b := by simp
  le_sup_right : ∀ a b : DemandedVL, b ≤ a ⊔ b := by simp
  sup_le : ∀ a b c : DemandedVL, a ≤ c → b ≤ c → a ⊔ b ≤ c := by
    intro a b c hac hbc
    rcases @DemandedVL.max_either a b with h | h <;> rw [h] <;> assumption

/-- Instructions are mapped to the natural numbers. -/
abbrev Instr := Nat

/--
Our DemandedVL map is a map from instructions to DemandedVLs.
Instructions might not be in the map, hence the Option.

Represents the DenseMap<const MachineInstr *, DemandedVL> in RISCVVLOptimizer.cpp
-/
abbrev Map := Instr -> Option DemandedVL

/-- Function/'Extensional' encoding of maps -/
def Map.empty : Map := fun _ =>  none

def Map.top : Map := fun _ => .some .vlmax

theorem Map.top_get (v : Instr) : Map.top v = .some .vlmax := by
  simp [Map.top]

def joinOptionDemandedVL  (a b : Option DemandedVL) : Option DemandedVL  :=
  match a, b with
  | .none, x => x
  | y, .none => y
  | .some x, .some y => .some (x ⊔ y)

@[simp]
theorem joinOptionDemandedVL_none_eq {a : Option DemandedVL} :
  joinOptionDemandedVL a none = a := by
  rcases a with rfl | a <;> simp [joinOptionDemandedVL]

@[simp]
theorem none_joinOptionDemandedVL_eq {a : Option DemandedVL} :
  joinOptionDemandedVL none a = a := by
  rcases a with rfl | a <;> simp [joinOptionDemandedVL]


@[simp]
theorem some_joinOptionDemandedVL_some_eq {a b : DemandedVL} :
  joinOptionDemandedVL (some a) (some b) = some (a ⊔ b) := by
  rcases a with rfl | a <;> simp [joinOptionDemandedVL]

@[simp]
theorem joinOptionDemandedVL_comm {a b : Option DemandedVL} :
  joinOptionDemandedVL a b = joinOptionDemandedVL b a := by
  rcases a with rfl | a <;> rcases b with rfl | b <;> simp [joinOptionDemandedVL]


@[simp]
theorem joinOptionDemandedVL_idem {a : Option DemandedVL} :
   joinOptionDemandedVL a a = a := by
  rcases a with rfl | a <;>
  simp [joinOptionDemandedVL]

def Map.join (a b : Map) : Map :=
  fun v => joinOptionDemandedVL (a v) (b v)

@[simp]
instance : Max (Map) where
  max := Map.join

def Map.singleton (v : Instr) (l : Option DemandedVL) : Map :=
  fun w => if v = w then l else .none

def Map.insert (v : Instr) (l : DemandedVL) (map : Map) : Map :=
   fun w => if v = w then .some l else map w

def Map.mem? (m : Map) (i : Instr) : Prop :=
    ∃ (l : DemandedVL), (m i) = some l

instance : LE (Option DemandedVL) where
  le (l1 l2 : (Option DemandedVL)) : Prop :=
  match l1, l2 with
    | .none, _ => true
    | .some a, .some b => a ≤ b
    | .some _, .none => false

@[simp]
theorem none_LeOptionDemandedVL {a : Option DemandedVL} : none ≤ a := by
  rcases a with rfl | a <;> simp [instLEOptionDemandedVL]

@[simp]
theorem LeOptionDemandedVL_some_vlmax {a : Option DemandedVL} : a ≤ (some .vlmax) := by
  rcases a with rfl | a <;> simp [instLEOptionDemandedVL]

@[refl, simp]
theorem LeOptionDemandedVL_refl {a : Option DemandedVL} : a ≤ a := by
  cases a <;> simp [instLEOptionDemandedVL]

@[simp]
theorem LeOptionDemandedVL_antisymm {a b : Option DemandedVL} : a ≤ b → b ≤ a → a = b := by
  intros
  match a, b with
  | .none, .none => rfl
  | .some a, .some b =>
    simp_all [instLEOptionDemandedVL]
    apply DemandedVL.le_antisymm <;> assumption


@[simp]
theorem optionDemandedVLLENone { x : Option DemandedVL } : x ≤ none → x = none := by
  intros
  cases x
  · rfl
  · apply LeOptionDemandedVL_antisymm
    assumption
    simp

@[simp]
theorem liftOptionDemandedVLLE { a b : DemandedVL } : (some a ≤ some b) = (a ≤ b) := rfl

@[simp]
theorem LeOptionDemandedVL_vlmax_le_iff_eq {a : Option DemandedVL} : some .vlmax ≤ a ↔ a = some .vlmax := by
  cases a <;> simp_all only [instLEOptionDemandedVL]
  · constructor <;> (intros; contradiction)
  · constructor
    · intros
      apply LeOptionDemandedVL_antisymm
      exact LeOptionDemandedVL_some_vlmax
      apply liftOptionDemandedVLLE.mp
      assumption
    · simp_all

@[simp]
theorem optionDemandedVLSomeNotLENone { x : DemandedVL } : ¬ some x ≤ none := by
  simp only [instLEOptionDemandedVL, Bool.false_eq_true]
  exact fun a => a

@[simp]
theorem optionDemandedVL_neq_le_not_le {a b : Option DemandedVL} : a ≤ b → a ≠ b → ¬ b ≤ a := by
  cases a <;> cases b <;> simp_all

@[simp]
theorem LeOptionDemandedVL_trans {a b c : Option DemandedVL}
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    a ≤ c := by
  rcases a with rfl | la <;>
  rcases b with rfl | lb <;>
  rcases c with rfl | lc <;> simp_all only [instLEOptionDemandedVL, Bool.false_eq_true]
  · apply DemandedVL.le_trans <;> assumption

@[simp]
theorem joinOptionDemandedVL_eq_right_of_le (a b : Option DemandedVL) (hab : a ≤ b) :
    joinOptionDemandedVL a b = b := by
  simp only [joinOptionDemandedVL]
  simp only [instLEOptionDemandedVL, Bool.false_eq_true] at hab
  rcases a with rfl | la <;>
  rcases b with rfl | lb <;>
  simp_all

theorem laneCountMax_max_le {a b c : DemandedVL} (hac : a ≤ c) (hbc : b ≤ c) :
  a ⊔ b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem LeOptionlaneCount_join_le {a b c : Option DemandedVL} (hac : a ≤ c) (hbc : b ≤ c) :
  joinOptionDemandedVL a b ≤ c := by
  simp [joinOptionDemandedVL]
  cases a <;> cases b <;> cases c <;> simp_all [laneCountMax_max_le]

/-- We know that a ≤ b iff there exists an 'x' such that `a join x = b`. -/
theorem LeOptionDemandedVL_iff_exists_joinOptionDemandedVL_eq {a b : Option DemandedVL} :
    a ≤ b ↔ ∃ (x : Option DemandedVL), joinOptionDemandedVL a x = b := by
  constructor
  · intros hx
    simp only [instLEOptionDemandedVL] at hx
    rcases a with rfl | la <;>
    rcases b with rfl | lb <;>
    simp_all
    exists (some lb)
    simp [hx]
  · intros hx
    obtain ⟨x, hx⟩ := hx
    simp only [joinOptionDemandedVL] at hx
    simp only [instLEOptionDemandedVL, Bool.false_eq_true]
    rcases a with rfl | la <;>
    rcases b with rfl | lb <;>
    rcases x with rfl | lx <;> simp_all only <;> try simp only [reduceCtorEq] at hx
    · simp at hx; subst hx; simp
    · simp at hx; subst hx; simp

instance : LE (Map) where
  le (a b : Map) : Prop :=
    ∀ (v : Instr), a v ≤ b v

/-- Le is reflexive. -/
@[refl, simp]
theorem Map.le?_refl (m : Map) : m ≤ m := by
  intro i
  apply LeOptionDemandedVL_refl

/-- Le is antisymmetric -/
theorem Map.le?_antisymm (m1 m2 : Map)
    (h1 : m1 ≤ m2) (h2 : m2 ≤ m1) : m1 = m2 := by
  ext v lv
  specialize (h1 v)
  specialize (h2 v)
  have := LeOptionDemandedVL_antisymm h1 h2
  simp [this]

/-- Le is transitive -/
@[simp]
theorem Map.le?_trans {m1 m2 m3 : Map}
    (h12 : m1 ≤ m2) (h23 : m2 ≤ m3) : m1 ≤ m3 := by
  intros v
  specialize (h12 v)
  specialize (h23 v)
  apply LeOptionDemandedVL_trans <;> assumption


instance {m : Map} {i : Instr} : Decidable (Map.mem? m i) :=
  if hl : (m i).isSome
  then .isTrue (by simp [hl, Map.mem?]; exact Option.isSome_iff_exists.mp hl)
  else .isFalse (by simp [Map.mem?]; intros x hx; simp [hx] at hl)

/-- A semilattice is a commutative idempotent monoid, which is compatible with the ordering. -/

@[simp]
theorem Map.join_comm {p q : Map} : p.join q = q.join p := by
  ext v lv
  simp [Map.join]

/-- Map join is idempotent -/
theorem Map.join_idem {p : Map} : p.join p = p := by
  ext v lv
  simp [Map.join]

/-- Empty is identity. -/
theorem Map.empty_join_eq {p : Map} : (Map.empty).join p = p := by
  ext v lv
  simp [Map.join, Map.empty]

/-- Empty is identity. -/
theorem Map.join_empty_eq {p : Map} : p.join (Map.empty) = p := by
  ext v lv
  simp [Map.join, Map.empty]

/-- Extensionality principle for maps -/
theorem Map.eq_iff_ext_eq {p q : Map} :  p = q ↔  (∀ v, p v = q v) := by
  constructor
  · intros h; subst h; simp
  · intros h; ext v lv; rw [h v]

@[ext]
theorem Map.ext {p q : Map} (h : ∀ v, p v = q v) : p = q := by
  apply Map.eq_iff_ext_eq.mpr h

theorem Map.le_ext {p q : Map} : p ≤ q ↔ ∀ v, p v ≤ q v := by
   simp [instLEMap]

/-- Le is compatoble with join: a ≤ b iff exists m, a.join m = b -/
theorem Map.le_iff_exists_join_eq {a b : Map} :
    a ≤ b ↔ (∃ m, a.join m = b) := by
  constructor
  simp [instLEMap]
  · intros hle
    exists b
    ext w lvw
    simp [Map.join, hle w]
  · simp [Map.join, instLEMap]
    intros x hx
    intros v
    have  this : (a.join x) v = (b v) := by simp [hx]
    simp [Map.join] at this
    apply LeOptionDemandedVL_iff_exists_joinOptionDemandedVL_eq.mpr
    exists (x v)

theorem Map.le_join? {a b : Map} : a ≤ a.join b := by
  intro v
  simp [Map.join]
  apply LeOptionDemandedVL_iff_exists_joinOptionDemandedVL_eq.mpr
  exists (b v)

instance : Preorder (Map) where
  le_refl (a : Map) : a ≤ a := by rfl
  le_trans (a b c : Map) : a ≤ b → b ≤ c → a ≤ c := by
    intros
    apply Map.le?_trans <;> assumption

instance : PartialOrder (Map) where
  le_antisymm (a b : Map) : a ≤ b → b ≤ a → a = b := by
    intros
    apply Map.le?_antisymm <;> assumption

instance : SemilatticeSup (Map) where
  sup := Map.join
  le_sup_left : ∀ a b : Map, a ≤ a.join b := by
    intros
    exact Map.le_join?
  le_sup_right : ∀ a b : Map, b ≤ a.join b := by
    intros a b
    rw [Map.join_comm]
    exact Map.le_join?
  sup_le : ∀ a b c : Map, a ≤ c → b ≤ c → a.join b ≤ c := by
    intros
    simp [instLEMap, Map.join]
    intros
    apply LeOptionlaneCount_join_le <;> apply Map.le_ext.mp <;> assumption

theorem Map.le_all_none {a b : Map} : ∀ v, a ≤ b → b v = none → a v = none := by
  intro v h h2
  simp [instLEMap] at h
  have h3 : a v ≤ b v := h v
  rw [h2] at h3
  exact optionDemandedVLLENone h3

theorem Map.join_empty {a b: Map} : ∀ v, b v = none → (a.join b) v = a v := by
  intros
  simp [instLEMap, Map.join]
  simp [*]

theorem Map.join_either {a b: Map} : ∀ v, (a.join b v = a v) ∨ (a.join b v = b v) := by
  intro v
  simp [Map.join, joinOptionDemandedVL]
  cases a v <;> cases b v <;> simp; apply LinearOrder.le_total

-- a ≤ b => a ∪ c ≤ b ∪ c
theorem Map.join_monotone {a b c : Map} (hab : a ≤ b) : (a.join c) ≤ (b.join c) := by
  intro v
  cases @Map.join_either a c v with
  | inl h =>
    rw [h]
    apply Map.le?_trans hab
    exact Map.le_join?
  | inr h => rw [h]; exact (SemilatticeSup.le_sup_right b c) v

-- a ≤ a' => b ≤ b' => a ∪ b ≤ a' ∪ b'
theorem Map.join_le_join_of_le_of_le {a a' b b' : Map} (hab : a ≤ a') (hbc : b ≤ b') :
  (a.join b) ≤ (a'.join b') := by
  simp [instLEMap]
  intro v
  rcases @Map.join_either a b v with h | h <;> cases @Map.join_either a' b' v
  repeat
    rw [h]
    apply Map.le?_trans
    assumption
    try apply SemilatticeSup.le_sup_right
    try apply SemilatticeSup.le_sup_left

@[simp]
theorem Map.bot_le {p : Map} : (Map.empty) ≤ p := by
  intro v
  constructor

theorem Map.le_top {p : Map} : p ≤ Map.top := by
  intro v
  simp [top]


 -- ∀ x, x ∈ join a b ↔ x ∈ a ∨ x ∈ b := b
theorem mem_join_iff_mem_or_mem : ∀ (i : Instr) (p q : Map), (p.join q).mem? i ↔ p.mem? i ∨ q.mem? i := by
  intros i p q
  constructor
  · simp [Map.join, Map.mem?, joinOptionDemandedVL]
    intros l
    rcases hp : p i with _ | pval
    · simp [hp]
      intros hq
      simp [hq]
    · simp [hp]
  · simp [Map.join, Map.mem?, joinOptionDemandedVL]
    intros h
    rcases h with hp | hq
    · obtain ⟨pl, hpl⟩ := hp
      rcases hq : q i with _ | qval
      · simp [hpl, hq]
      · simp [hpl, hq]
    · obtain ⟨ql, hql⟩ := hq
      simp [hql]
      rcases hp : p i with _ | pval
      · simp [hp]
      · simp [hp]


def optionDemandedVLMin : Option DemandedVL → Option DemandedVL → Option DemandedVL
  | .none, _ => none
  | _, .none => none
  | .some a, .some b => if a ≤ b then .some a else .some b

@[simp]
theorem optionDemandedVLMinNone (x : Option DemandedVL) : (optionDemandedVLMin .none x) = .none := by
  simp [optionDemandedVLMin]

@[simp]
theorem noneOptionDemandedVLMin (x : Option DemandedVL) : (optionDemandedVLMin x .none) = .none := by
  cases x <;> simp [optionDemandedVLMin]

@[simp]
theorem optionDemandedVLVLMax {x : Option DemandedVL} : (optionDemandedVLMin x (some .vlmax)) = x := by
  cases x <;> simp [optionDemandedVLMin]

@[simp]
theorem optionDemandedVLVLMax2 {x : Option DemandedVL} : (optionDemandedVLMin (some .vlmax) x) = x := by
  simp [optionDemandedVLMin]
  cases x <;> simp_all

theorem optionDemandedVLMin_comm (a b : Option DemandedVL) :
  optionDemandedVLMin a b = optionDemandedVLMin b a :=
  match a, b with
    | .none, _ => by simp_all
    | _, .none => by simp_all
    | .some .vlmax, .some b1 => by simp
    | .some _, .some .vlmax => by simp
    | some (.vlconst a1), some (.vlconst b1) => by
      simp only [optionDemandedVLMin]
      by_cases hle : a1 ≤ b1
      · simp_all
        by_cases heq : a1 = b1
        · simp_all
        · have hbnlea : ¬ b1 ≤ a1 := by simp; omega
          simp [hbnlea]
      · simp_all
        by_cases heq : a1 = b1
        · simp_all
        · have hbnlea : ¬ a1 ≤ b1 := by simp; omega
          simp [hbnlea, heq]
          simp [Nat.le_of_not_ge hbnlea]

theorem Map.singleton_le_of_le {i : Instr} (a b : Option DemandedVL)
    (hab : a ≤ b) :
    (Map.singleton i a) ≤ (Map.singleton i b) := by
 simp [instLEMap]
 intros v
 simp [Map.singleton]
 by_cases hi : i = v <;> simp_all [hi]

@[simp]
theorem DemandedVL.not_le_iff_le (a b : DemandedVL) (hab : ¬ a ≤ b) : b ≤ a := by
  revert hab
  simp [instLEDemandedVL]
  rcases a with rfl | a <;> rcases b with rfl | b <;> simp_all ; omega

theorem optionDemandedVLMin_le_of_le_of_le (a b b' : Option DemandedVL)
    (hb : b ≤ b') :
    (optionDemandedVLMin a b) ≤ (optionDemandedVLMin a b') := by
  rcases a with rfl | a <;> rcases b with rfl | b <;> rcases b' with rfl | b' <;>
    simp_all [optionDemandedVLMin]
  by_cases hab : a ≤ b <;> simp [hab]
  · by_cases hab' : a ≤ b' <;> simp [hab']
    have _ : a ≤ b' := by apply le_trans <;> assumption
    contradiction
  · by_cases hab' : a ≤ b' <;> simp [hb, hab, hab']

opaque instr_vls : Instr → Option DemandedVL

def transfer (i : Instr) (x : Map) : Map :=
  x.join (Map.singleton i (optionDemandedVLMin (x i) (instr_vls i)))

theorem transfer_monotonic (i : Instr) (x y : Map)
    (hxy : x ≤ y) : (transfer i x) ≤ (transfer i y) := by
  rw [transfer, transfer]
  apply Map.join_le_join_of_le_of_le
  · exact hxy
  · apply Map.singleton_le_of_le
    rw [optionDemandedVLMin_comm (x i), optionDemandedVLMin_comm (y i)]
    apply optionDemandedVLMin_le_of_le_of_le
    apply hxy
