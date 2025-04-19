import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice

inductive LaneCount
| vlmax
| vlconst (n : Nat)
deriving DecidableEq

instance : LE LaneCount where
  le (l1 l2 : LaneCount) : Prop :=
    match l1, l2 with
    | _, .vlmax => true
    | .vlmax, .vlconst _ => false
    | .vlconst a, .vlconst b => a <= b

def LaneCount.max (l1 l2 : LaneCount) : LaneCount :=
  match l1, l2 with
  | .vlmax, _ => .vlmax
  | _, .vlmax => .vlmax
  | .vlconst a, .vlconst b => .vlconst (a.max b) -- TODO: is this correct?

@[simp]
theorem LaneCount.max_comm {l1 l2 : LaneCount} : l1.max l2 = l2.max l1 := by
 rcases l1 with rfl | l1 <;> rcases l2 with rfl | l2 <;> simp [LaneCount.max, Nat.max, Nat.max_comm]

@[simp]
theorem LaneCount.max_idem {l : LaneCount} : l.max l = l := by
 rcases l with rfl | l <;> simp [LaneCount.max]

theorem LaneCount.max_either {l1 l2 : LaneCount} : l1.max l2 = l1 ∨ l1.max l2 = l2 := by
  cases l1 <;> cases l2 <;> simp [LaneCount.max]; exact Nat.le_total _ _

instance (l1 l2 : LaneCount) : Decidable (l1 ≤ l2) := by
  cases l1 with
  | vlmax => cases l2 <;> simp [LE.le] <;> infer_instance
  | vlconst n1 => cases l2 with
    | vlmax => simp [LE.le]; infer_instance
    | vlconst n2 => exact inferInstanceAs (Decidable (n1 ≤ n2))

@[simp]
theorem LaneCount.le?_vlmax (l : LaneCount) : l ≤ .vlmax := by
  rcases l with rfl | l <;> simp [LE.le]

@[simp]
theorem LaneCount.le_self_max (l1 l2 : LaneCount) : l1 ≤ (l1.max l2) := by
  rcases l1 with rfl | l1 <;> rcases l2 with rfl | l2 <;> simp [instLELaneCount, LaneCount.max, Nat.max]


@[simp]
theorem LaneCount.le_max_self (l1 l2 : LaneCount) : l1 ≤ (l2.max l1) := by
  rcases l1 with rfl | l1 <;> rcases l2 with rfl | l2 <;> simp [instLELaneCount, LaneCount.max, Nat.max]

/-- Le is reflexive -/
@[refl, simp]
theorem LaneCount.le_refl (l : LaneCount) : l ≤ l := by cases l <;> simp [instLELaneCount]

namespace LaneCount

variable {a b c : LaneCount}

/-- Le is antisymmetric -/
@[simp]
theorem le_antisymm_iff : a ≤ b ∧ b ≤ a ↔ (a = b) := by
  cases a <;> cases b <;> simp [instLELaneCount, antisymm_iff]

@[simp]
theorem le_antisymm : ∀ a b : LaneCount, a ≤ b → b ≤ a → a = b := by
  intros a b; cases a <;> cases b <;> simp [instLELaneCount]; omega

/-- Le is transitive -/
@[simp]
theorem le_trans : a ≤ b → b ≤ c → a ≤ c := by
  rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;>
    simp [instLELaneCount]; apply Nat.le_trans

@[simp]
theorem max_eq_left_of_le : a ≤ b → a.max b = b := by
  cases a <;> cases b <;> simp [instLELaneCount, LaneCount.max, Nat.max]

@[simp]
theorem max_eq_right_of_le : b ≤ a → a.max b = a := by
  cases a <;> cases b <;> simp [instLELaneCount, LaneCount.max, Nat.max]

@[simp]
theorem le_nat {a b : Nat} : (vlconst a ≤ vlconst b) = (a ≤ b) := by rfl

@[simp]
theorem neq_le_not_le : a ≤ b → a ≠ b → ¬ b ≤ a := by
  cases a <;> cases b <;> simp [instLELaneCount]; omega

@[simp]
theorem vlmax_le : vlmax ≤ a ↔ a = vlmax := by
  cases a <;> simp [instLELaneCount]


end LaneCount

instance : Preorder LaneCount where
  le_refl (a : LaneCount) : a ≤ a := LaneCount.le_refl a
  le_trans (a b c : LaneCount) : a ≤ b → b ≤ c → a ≤ c := LaneCount.le_trans

instance : PartialOrder LaneCount where
  le_antisymm := LaneCount.le_antisymm

instance : SemilatticeSup LaneCount where
  sup := LaneCount.max
  le_sup_left : ∀ a b : LaneCount, a ≤ a.max b := by
    intros a b
    simp [LaneCount.max]
    cases a <;> cases b <;> simp
  le_sup_right : ∀ a b : LaneCount, b ≤ a.max b := by
    simp
  sup_le : ∀ a b c : LaneCount, a ≤ c → b ≤ c → a.max b ≤ c := by
    intro a b c hac hbc
    rcases @LaneCount.max_either a b with h | h <;> rw [h] <;> assumption

/-- Map -/
abbrev Map (n : Nat) := Fin n -> Option LaneCount

/-- Function/'Extensional' encoding of maps -/
def Map.empty (n : Nat) : Map n := fun _ =>  none

def Map.top (n : Nat) : Map n := fun _ => .some .vlmax

theorem Map.top_get (n : Nat) (v : Fin n) : Map.top n v = .some .vlmax := by
  simp [Map.top]

def joinOptionLaneCount  (a b : Option LaneCount) : Option LaneCount  :=
  match a, b with
  | .none, x => x
  | y, .none => y
  | .some x, .some y => .some (x.max y)

@[simp]
theorem joinOptionLaneCount_none_eq {a : Option LaneCount} :
  joinOptionLaneCount a none = a := by
  rcases a with rfl | a <;> simp [joinOptionLaneCount]

@[simp]
theorem none_joinOptionLaneCount_eq {a : Option LaneCount} :
  joinOptionLaneCount none a = a := by
  rcases a with rfl | a <;> simp [joinOptionLaneCount]


@[simp]
theorem some_joinOptionLaneCount_some_eq {a b : LaneCount} :
  joinOptionLaneCount (some a) (some b) = some (a.max b) := by
  rcases a with rfl | a <;> simp [joinOptionLaneCount]

@[simp]
theorem joinOptionLaneCount_comm {a b : Option LaneCount} :
  joinOptionLaneCount a b = joinOptionLaneCount b a := by
  rcases a with rfl | a <;> rcases b with rfl | b <;> simp [joinOptionLaneCount]


@[simp]
theorem joinOptionLaneCount_idem {a : Option LaneCount} :
   joinOptionLaneCount a a = a := by
  rcases a with rfl | a <;>
  simp [joinOptionLaneCount]

def Map.join {n : Nat} (a b : Map n) : Map n :=
  fun v => joinOptionLaneCount (a v) (b v)

@[simp]
instance {n : Nat} : Max (Map n) where
  max := Map.join

def Map.singleton {n : Nat} (v : Fin n) (l : LaneCount) : Map n :=
  fun w => if v = w then .some l else .none

def Map.singletonOption {n : Nat} (v : Fin n) (l : Option LaneCount) : Map n :=
  fun w => if v = w then l else .none

def Map.insert {n : Nat} (v : Fin n) (l : LaneCount) (map : Map n) : Map n :=
   (Map.singleton v l).join map

def Map.mem? {n : Nat} (m : Map n) (v : Fin n) : Prop :=
    ∃ (l : LaneCount), (m v) = some l

instance : LE (Option LaneCount) where
  le (l1 l2 : (Option LaneCount)) : Prop :=
  match l1, l2 with
    | .none, _ => true
    | .some a, .some b => a ≤ b
    | .some _, .none => false

@[simp]
theorem none_LeOptionLaneCount {a : Option LaneCount} : none ≤ a := by
  rcases a with rfl | a <;> simp [instLEOptionLaneCount]

@[simp]
theorem LeOptionLaneCount_some_vlmax {a : Option LaneCount} : a ≤ (some .vlmax) := by
  rcases a with rfl | a <;> simp [instLEOptionLaneCount]

@[refl, simp]
theorem LeOptionLaneCount_refl {a : Option LaneCount} : a ≤ a := by
  cases a <;> simp [instLEOptionLaneCount]

@[simp]
theorem LeOptionLaneCount_antisymm {a b : Option LaneCount} : a ≤ b → b ≤ a → a = b := by
  intros
  match a, b with
  | .none, .none => rfl
  | .some a, .some b =>
    simp_all [instLEOptionLaneCount]
    apply LaneCount.le_antisymm <;> assumption


@[simp]
theorem optionLaneCountLENone { x : Option LaneCount } : x ≤ none → x = none := by
  intros
  cases x
  · rfl
  · apply LeOptionLaneCount_antisymm
    assumption
    simp

@[simp]
theorem liftOptionLaneCountLE { a b : LaneCount } : (some a ≤ some b) = (a ≤ b) := rfl

@[simp]
theorem LeOptionLaneCount_vlmax_le_iff_eq {a : Option LaneCount} : some .vlmax ≤ a ↔ a = some .vlmax := by
  cases a <;> simp_all only [instLEOptionLaneCount]
  · constructor <;> (intros; contradiction)
  · constructor
    · intros
      apply LeOptionLaneCount_antisymm
      exact LeOptionLaneCount_some_vlmax
      apply liftOptionLaneCountLE.mp
      assumption
    · simp_all

@[simp]
theorem optionLaneCountSomeNotLENone { x : LaneCount } : ¬ some x ≤ none := by
  simp only [instLEOptionLaneCount, Bool.false_eq_true]
  exact fun a => a

@[simp]
theorem optionLaneCount_neq_le_not_le {a b : Option LaneCount} : a ≤ b → a ≠ b → ¬ b ≤ a := by
  cases a <;> cases b <;> simp_all

@[simp]
theorem LeOptionLaneCount_trans {a b c : Option LaneCount}
    (hab : a ≤ b)
    (hbc : b ≤ c) :
    a ≤ c := by
  rcases a with rfl | la <;>
  rcases b with rfl | lb <;>
  rcases c with rfl | lc <;> simp_all only [instLEOptionLaneCount, Bool.false_eq_true]
  · apply LaneCount.le_trans <;> assumption

@[simp]
theorem joinOptionLaneCount_eq_right_of_le (a b : Option LaneCount) (hab : a ≤ b) :
    joinOptionLaneCount a b = b := by
  simp only [joinOptionLaneCount]
  simp only [instLEOptionLaneCount, Bool.false_eq_true] at hab
  rcases a with rfl | la <;>
  rcases b with rfl | lb <;>
  simp_all

theorem laneCountMax_max_le {a b c : LaneCount} (hac : a ≤ c) (hbc : b ≤ c) :
  a.max b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [LaneCount.max]

theorem LeOptionlaneCount_join_le {a b c : Option LaneCount} (hac : a ≤ c) (hbc : b ≤ c) :
  joinOptionLaneCount a b ≤ c := by
  simp [joinOptionLaneCount]
  cases a <;> cases b <;> cases c <;> simp_all [laneCountMax_max_le]

/-- We know that a ≤ b iff there exists an 'x' such that `a join x = b`. -/
theorem LeOptionLaneCount_iff_exists_joinOptionLaneCount_eq {a b : Option LaneCount} :
    a ≤ b ↔ ∃ (x : Option LaneCount), joinOptionLaneCount a x = b := by
  constructor
  · intros hx
    simp only [instLEOptionLaneCount] at hx
    rcases a with rfl | la <;>
    rcases b with rfl | lb <;>
    simp_all
    exists (some lb)
    simp [hx]
  · intros hx
    obtain ⟨x, hx⟩ := hx
    simp only [joinOptionLaneCount] at hx
    simp only [instLEOptionLaneCount, Bool.false_eq_true]
    rcases a with rfl | la <;>
    rcases b with rfl | lb <;>
    rcases x with rfl | lx <;> simp_all only <;> try simp only [reduceCtorEq] at hx
    · simp at hx; subst hx; simp
    · simp at hx; subst hx; simp

variable {n : Nat}

instance : LE (Map n) where
  le (a b : Map n) : Prop :=
    ∀ (v : Fin n), a v ≤ b v


/-- Le is reflexive. -/
@[refl, simp]
theorem Map.le?_refl (m : Map n) : m ≤ m := by
  intro v
  apply LeOptionLaneCount_refl

/-- Le is antisymmetric -/
theorem Map.le?_antisymm (m1 m2 : Map n)
    (h1 : m1 ≤ m2) (h2 : m2 ≤ m1) : m1 = m2 := by
  ext v lv
  specialize (h1 v)
  specialize (h2 v)
  have := LeOptionLaneCount_antisymm h1 h2
  simp [this]

/-- Le is transitive -/
@[simp]
theorem Map.le?_trans {m1 m2 m3 : Map n}
    (h12 : m1 ≤ m2) (h23 : m2 ≤ m3) : m1 ≤ m3 := by
  intros v
  specialize (h12 v)
  specialize (h23 v)
  apply LeOptionLaneCount_trans <;> assumption


instance {n : Nat} {m : Map n} {v : Fin n} : Decidable (Map.mem? m v) :=
  if hl : (m v).isSome
  then .isTrue (by simp [hl, Map.mem?]; exact Option.isSome_iff_exists.mp hl)
  else .isFalse (by simp [Map.mem?]; intros x hx; simp [hx] at hl)

/-- A semilattice is a commutative idempotent monoid, which is compatible with the ordering. -/

@[simp]
theorem Map.join_comm {p q : Map n} : p.join q = q.join p := by
  ext v lv
  simp [Map.join]

/-- Map join is idempotent -/
theorem Map.join_idem {p : Map n} : p.join p = p := by
  ext v lv
  simp [Map.join]

/-- Empty is identity. -/
theorem Map.empty_join_eq {p : Map n} : (Map.empty n).join p = p := by
  ext v lv
  simp [Map.join, Map.empty]

/-- Empty is identity. -/
theorem Map.join_empty_eq {p : Map n} : p.join (Map.empty n) = p := by
  ext v lv
  simp [Map.join, Map.empty]

/-- Extensionality principle for maps -/
theorem Map.eq_iff_ext_eq {p q : Map n} :  p = q ↔  (∀ v, p v = q v) := by
  constructor
  · intros h; subst h; simp
  · intros h; ext v lv; rw [h v]

@[ext]
theorem Map.ext {p q : Map n} (h : ∀ v, p v = q v) : p = q := by
  apply Map.eq_iff_ext_eq.mpr h

theorem Map.le_ext {p q : Map n} : p ≤ q ↔ ∀ v, p v ≤ q v := by
   simp [instLEMap]

/-- Le is compatoble with join: a ≤ b iff exists m, a.join m = b -/
theorem Map.le_iff_exists_join_eq {a b : Map n} :
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
    apply LeOptionLaneCount_iff_exists_joinOptionLaneCount_eq.mpr
    exists (x v)

theorem Map.le_join? {a b : Map n} : a ≤ a.join b := by
  intro v
  simp [Map.join]
  apply LeOptionLaneCount_iff_exists_joinOptionLaneCount_eq.mpr
  exists (b v)

instance : Preorder (Map n) where
  le_refl (a : Map n) : a ≤ a := by rfl
  le_trans (a b c : Map n) : a ≤ b → b ≤ c → a ≤ c := by
    intros
    apply Map.le?_trans <;> assumption

instance : PartialOrder (Map n) where
  le_antisymm (a b : Map n) : a ≤ b → b ≤ a → a = b := by
    intros
    apply Map.le?_antisymm <;> assumption

instance : SemilatticeSup (Map n) where
  sup := Map.join
  le_sup_left : ∀ a b : Map n, a ≤ a.join b := by
    intros
    exact Map.le_join?
  le_sup_right : ∀ a b : Map n, b ≤ a.join b := by
    intros a b
    rw [Map.join_comm]
    exact Map.le_join?
  sup_le : ∀ a b c : Map n, a ≤ c → b ≤ c → a.join b ≤ c := by
    intros
    simp [instLEMap, Map.join]
    intros
    apply LeOptionlaneCount_join_le <;> apply Map.le_ext.mp <;> assumption

theorem Map.le_all_none {a b : Map n} : ∀ v, a ≤ b → b v = none → a v = none := by
  intro v h h2
  simp [instLEMap] at h
  have h3 : a v ≤ b v := h v
  rw [h2] at h3
  exact optionLaneCountLENone h3

theorem Map.join_empty {a b: Map n} : ∀ v, b v = none → (a.join b) v = a v := by
  intros
  simp [instLEMap, Map.join]
  simp [*]

theorem Map.join_either {a b: Map n} : ∀ v, (a.join b v = a v) ∨ (a.join b v = b v) := by
  intro v
  simp [Map.join, joinOptionLaneCount]
  cases a v <;> cases b v <;> simp; exact LaneCount.max_either

-- a ≤ b => a ∪ c ≤ b ∪ c
theorem Map.join_monotone {a b c : Map n} (hab : a ≤ b) : (a.join c) ≤ (b.join c) := by
  intro v
  cases @Map.join_either n a c v with
  | inl h =>
    rw [h]
    apply Map.le?_trans hab
    exact Map.le_join?
  | inr h => rw [h]; exact (SemilatticeSup.le_sup_right b c) v

-- a ≤ a' => b ≤ b' => a ∪ b ≤ a' ∪ b'
theorem Map.join_le_join_of_le_of_le {a a' b b' : Map n} (hab : a ≤ a') (hbc : b ≤ b') :
  (a.join b) ≤ (a'.join b') := by
  simp [instLEMap]
  intro v
  rcases @Map.join_either n a b v with h | h <;> cases @Map.join_either n a' b' v
  repeat
    rw [h]
    apply Map.le?_trans
    assumption
    try apply SemilatticeSup.le_sup_right
    try apply SemilatticeSup.le_sup_left

@[simp]
theorem Map.bot_le {p : Map n} : (Map.empty n) ≤ p := by
  intro v
  constructor

theorem Map.le_top {p : Map n} : p ≤ Map.top n := by
  intro v
  simp [top]


 -- ∀ x, x ∈ join a b ↔ x ∈ a ∨ x ∈ b := b
theorem mem_join_iff_mem_or_mem {n : Nat} : ∀ (v : Fin n) (p q : Map n), (p.join q).mem? v ↔ p.mem? v ∨ q.mem? v := by
  intros v p q
  constructor
  · simp [Map.join, Map.mem?, joinOptionLaneCount]
    intros l
    rcases hp : p v with _ | pval
    · simp [hp]
      intros hq
      simp [hq]
    · simp [hp]
  · simp [Map.join, Map.mem?, joinOptionLaneCount]
    intros h
    rcases h with hp | hq
    · obtain ⟨pl, hpl⟩ := hp
      rcases hq : q v with _ | qval
      · simp [hpl, hq]
      · simp [hpl, hq]
    · obtain ⟨ql, hql⟩ := hq
      simp [hql]
      rcases hp : p v with _ | pval
      · simp [hp]
      · simp [hp]


def optionLaneCountMin : Option LaneCount → Option LaneCount → Option LaneCount
  | .none, _ => none
  | _, .none => none
  | .some a, .some b => if a ≤ b then .some a else .some b

@[simp]
theorem optionLaneCountMinNone (x : Option LaneCount) : (optionLaneCountMin .none x) = .none := by
  simp [optionLaneCountMin]

@[simp]
theorem noneOptionLaneCountMin (x : Option LaneCount) : (optionLaneCountMin x .none) = .none := by
  cases x <;> simp [optionLaneCountMin]

@[simp]
theorem optionLaneCountVLMax {x : Option LaneCount} : (optionLaneCountMin x (some .vlmax)) = x := by
  cases x <;> simp [optionLaneCountMin]

@[simp]
theorem optionLaneCountVLMax2 {x : Option LaneCount} : (optionLaneCountMin (some .vlmax) x) = x := by
  simp [optionLaneCountMin]
  cases x <;> simp_all

theorem optionLaneCountMin_comm (a b : Option LaneCount) :
  optionLaneCountMin a b = optionLaneCountMin b a :=
  match a, b with
    | .none, _ => by simp_all
    | _, .none => by simp_all
    | .some .vlmax, .some b1 => by simp
    | .some _, .some .vlmax => by simp
    | some (.vlconst a1), some (.vlconst b1) => by
      simp only [optionLaneCountMin]
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

def transfer (i : Fin n) (vl : Fin n → Option LaneCount) (x : Map n) : Map n :=
  x.join (Map.singletonOption i (optionLaneCountMin (x i) (vl i)))

theorem Map.singletonOption_le_of_le {i : Fin n} (a b : Option LaneCount)
    (hab : a ≤ b) :
    (Map.singletonOption i a) ≤ (Map.singletonOption i b) := by
 simp [instLEMap]
 intros v
 simp [singletonOption]
 by_cases hi : i = v <;> simp_all [hi]

@[simp]
theorem LaneCount.not_le_iff_le (a b : LaneCount) (hab : ¬ a ≤ b) : b ≤ a := by
  revert hab
  simp [instLELaneCount]
  rcases a with rfl | a <;> rcases b with rfl | b <;> simp_all ; omega

theorem optionLaneCountMin_le_of_le_of_le (a b b' : Option LaneCount)
    (hb : b ≤ b') :
    (optionLaneCountMin a b) ≤ (optionLaneCountMin a b') := by
  rcases a with rfl | a <;> rcases b with rfl | b <;> rcases b' with rfl | b' <;>
    simp_all [optionLaneCountMin]
  by_cases hab : a ≤ b <;> simp [hab]
  · by_cases hab' : a ≤ b' <;> simp [hab']
    have _ : a ≤ b' := by apply le_trans <;> assumption
    contradiction
  · by_cases hab' : a ≤ b' <;> simp_all [hab']



theorem transfer_monotonic (i : Fin n) (vl : Fin n → Option LaneCount) (x y : Map n)
    (hxy : x ≤ y) : (transfer i vl x) ≤ (transfer i vl y) := by
  rw [transfer, transfer]
  apply Map.join_le_join_of_le_of_le
  · exact hxy
  · apply Map.singletonOption_le_of_le
    rw [@optionLaneCountMin_comm (x i), @optionLaneCountMin_comm (y i)]
    apply optionLaneCountMin_le_of_le_of_le
    apply hxy
