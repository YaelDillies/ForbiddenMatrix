import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Synonym
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Logic.Equiv.Set
import Mathlib.LinearAlgebra.Matrix.Permutation

--Init.Control.Basic



--import Duper

--example : True := by duper


set_option linter.unusedTactic false
set_option maxHeartbeats 800000


namespace Finset
variable {ι α : Type*} [CanonicallyLinearOrderedAddCommMonoid α] {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']
@[simp] lemma non_zero (n :ℕ )[NeZero n] : 0 < n := by
  cases n
  simp_all [lt_self_iff_false]
  omega

end Finset

open Finset Set
open OrderDual
open Equiv
--open Fin
attribute [local irreducible] OrderDual

-- def trivialPattern : (α → β → Prop) := [1, 1, 1]
-- λ x : nat ↦ x + 5
-- variable {n : ℕ }
-- ![![a, b, c], ![b, c, d]] : matrix (fin 2) (fin 3) α
-- see https://leanprover-community.github.io/theories/linear_algebra.html
-- λ (i : m) (j : n), (_ : α)
def HatPattern : Fin 2 → Fin 3 → Prop :=
  ![
    ![false, true, false],
    ![true, false, true]
   ]
def HatPatternD : Fin 3 → Fin 2 → Prop :=
  ![
    ![true, false],
    ![false, true],
    ![true, false]
   ]
def VerticalTwoPattern : Fin 2 → Fin 1 → Prop :=
  ![
    ![true],
    ![true]
   ]
def Horizontal2Pattern : Fin 1 → Fin 2 → Prop := ![![true,true]]
def Horizontal3Pattern : Fin 1 → Fin 3 → Prop := ![![true,true,true]]


def Horizontal3Patternt : Fin 1 → Fin 3 → Fin 2 := ![![1,1,1]]
--def HatPatternFin: Fin 2 → Fin 3 → Bool :=
--  ![
--    ![0, 1, 0],
--    ![1, 0, 1]
--   ]
--#check HatPatternFin
def IdentityFin (n : ℕ) (i j : Fin n) : Fin 2 := if i = j then 1 else 0


def horizontalkPattern (k : ℕ) (_ :Fin 1) (_ : Fin k) : Prop := true
def verticalkPattern (k : ℕ) (_ :Fin k) (_ : Fin 1) : Prop := true
def identityPattern (n : ℕ) (i j : Fin n) : Prop := i = j
def revIdentityPattern (n : ℕ) (i j : Fin n) : Prop := i + j = n
--def IdentityF (n : ℕ) (i j : Fin n) : Fin 2 := (i = j :)
def Perm (k : ℕ) (i j : Fin k) : Prop := i = j
def onePattern : Fin 1 → Fin 1 → Prop := fun _ : Fin 1 => fun _ : Fin 1 => true
def IdentityB (n : ℕ) (i j : Fin n) : Bool := i = j
def PatternOneB : Fin 1 → Fin 1 → Bool := fun _ : Fin 1 => fun _ : Fin 1 => true


--variable {α  : Type*} [Preorder α]
--open scoped Classical in noncomputable
--def permPatternFin {k:ℕ}(σ : Equiv.Perm (Fin k)) := Equiv.Perm.permMatrix (Fin 2) σ

--def f : Fin 3 → Fin 3 := ![0,2,1 : Fin 3]

def permPatternFin {k:ℕ}(σ : Equiv.Perm (Fin k))  (i j : Fin k): Fin 2 := (Equiv.Perm.permMatrix (Fin 2) σ) i j
def permPattern {k:ℕ}(σ : Equiv.Perm (Fin k))  (i j : Fin k): Prop := (Equiv.Perm.permMatrix ℕ σ) i j = 1
--def identity (k :ℕ) (i : Fin k) : Fin k := i
--#eval  (One (Fin 2))
--def f : Fin 2 → Fin 2 := ![0,1]
def permid : Equiv.Perm (Fin 3) := Equiv.refl (Fin 3)
--#eval permPattern permid


--#check permPattern (identity 3)
--#check permPattenFin
--open Matrix
--section matrices



section contains
variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

-- TODO: replace StrictMono f by StrictMonoOn {a ∣ ∃ b, P a b} f, and similarly for g to ignore blank rows/columns
def contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

def containsB (P : α → β → Bool) (M : γ → δ → Bool) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

instance [Fintype α] [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : γ → γ → Prop)] {f : α → γ} :
  Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

instance {P : α → β → Bool} {M : γ → δ → Bool}
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    [DecidableRel (· < · : γ → γ → Prop)] [DecidableRel (· < · : δ → δ → Prop)]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] :
    Decidable (containsB P M) :=
  inferInstanceAs (Decidable (∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)))

lemma reflect_contain (M : γ → δ → Prop) : contains M M := by
  refine ⟨id, by simp [StrictMono],id, by simp [StrictMono], ?_ ⟩
  aesop

end contains


variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
open scoped Classical in noncomputable
def densityRect {n m :ℕ} (M : Fin n → Fin m → Prop)  : ℕ :=  ({(i, j) : Fin n × Fin m | M i j} : Finset (Fin n × Fin m)).card
--open scoped Classical in noncomputable def density (M : α → β → Prop) : ℕ := card {(i, j) : α × β | M i j}
open scoped Classical in noncomputable
def density {n:ℕ} (M : Fin n → Fin n → Prop)  : ℕ := ({(i, j) : Fin n × Fin n | M i j} : Finset (Fin n × Fin n)).card

open scoped Classical in noncomputable
def row_density {n:ℕ } (M : Fin n → Fin n → Prop) (i : Fin n): ℕ := ({j | M i j} : Finset (Fin n)).card

open scoped Classical in noncomputable def exRect (P : α → β → Prop) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Prop | ¬ contains P M} fun M ↦ densityRect M--card {(i, j) : Fin n × Fin m | M i j}

def exRectB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) (m : ℕ) : ℕ :=
  sup {M : Fin n → Fin m → Bool | ¬ containsB P M} fun M ↦ card {ij : Fin n × Fin m | M ij.1 ij.2}

open scoped Classical in noncomputable
def ex (P : α → β → Prop) (n : ℕ) : ℕ :=
   sup {M : Fin n → Fin n → Prop | ¬ contains P M} fun M ↦ density M

def exB [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [DecidableRel (· < · : α → α → Prop)] [DecidableRel (· < · : β → β → Prop)]
    (P : α → β → Bool) (n : ℕ) : ℕ :=
  exRectB P n n

--def Identity (n : ℕ) (i j : Fin n) : Prop := i = j


def L'' : Fin 2 → Fin 2 → Prop :=
  ![
    ![false, true],
    ![true, true]
  ]

def A' : Fin 2 → Fin 1 → Prop :=
  ![![true], ![false]]
def B' : Fin 2 → (Fin 1) → Prop :=
  ![![false], ![true]]

--def C' : (Fin 3)ᵒᵈ  → Bool := ![true,false,false]

--Matrix.of
--Fin.revOrderIso

def tranpose (M : α → β → Prop) : β → α  → Prop := fun x y ↦ M y x
def rev_all_rows (M : α → β → Prop) : α  → βᵒᵈ  → Prop :=  fun i ↦ (M i) ∘ ofDual
--def rot_cw (M : α → β → Prop) :  β → α ᵒᵈ → Prop := (rev_all_rows ∘ tranpose) M
def rot_cw (M : α → β → Prop) :  β → α ᵒᵈ → Prop := (rev_all_rows ∘ tranpose) M

def rev_all_rows_via_list {n : ℕ} (M : α → Fin n → Prop) : α → Fin n → Prop :=
   fun i ↦
    let v := Mathlib.Vector.ofFn (M i)
    let rv := v.reverse
    fun j : Fin n ↦ rv.get j

--def tranpose (M : α → β → Prop) : β → α  → Prop := fun x y ↦ M y x
--#check rev_all_rows B
def L : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, false],
    ![true, true]
   ]
def L' : Fin 2 → Fin 2 → Prop :=
  ![
    ![true, true],
    ![true, false]
  ]


def X : (Fin 3)ᵒᵈ → Bool := ![true,false,false] ∘ ofDual
def Y : Fin 3 → Bool := ![false,false,true]

def A : Fin 1 → Fin 2 → Prop := ![![true, false]]
def B : Fin 1 → (Fin 2)ᵒᵈ → Prop := ![![true, false]∘ ofDual]
def C : Fin 1 → (Fin 2) → Prop := ![![false, true]]

#check fun i ↦ (C i) ∘ Fin.revOrderIso
#check fun i ↦ (B i)

example : (fun i ↦ (C i) ∘ Fin.revOrderIso∘ toDual)  = fun i ↦ (rev_all_rows A i)∘ toDual := by
  ext i j
  simp [rev_all_rows,A,C]
  fin_cases i ; fin_cases j <;> simp [Fin.last,Fin.rev]

-- eample : B2 =    := by
--  ext
--  simp [rev_all_rows,A,B]

--def b : (Fin 2)ᵒᵈ → Bool := ![false, true] \comp ofDual
--#eval b (toDual 0)

-- the elements of (Fin 2)ᵒᵈ are, in order, toDual 1 and toDual 0
def a : Fin 2 → Bool := ![true, false]
-- b = rev_all_rows c
def c : Fin 2 → Bool := ![false, true]
def b : (Fin 2)ᵒᵈ → Bool := ![false, true]  ∘ ofDual

#eval  (a ∘ Fin.revOrderIso) (toDual 0) = b (toDual 0)
#eval  (a ∘ Fin.revOrderIso) (toDual 1) = b (toDual 1)


example : a ∘ Fin.revOrderIso  =  b  := by
  ext x
  --have:= OrderDual.toDual.surjective x
  --obtain ⟨y,h⟩  :=this
  --rw [← h]
  -- one line version of above
  obtain ⟨y, rfl⟩ := OrderDual.toDual.surjective x
  fin_cases y <;> rfl

example : a ∘ Fin.revOrderIso ∘ toDual =  b  ∘ toDual := by
  ext x
  fin_cases x <;> rfl


example : A = rev_all_rows_via_list C := by
  simp [A, C]
  ext a b
  rw [rev_all_rows_via_list]
  simp [Mathlib.Vector.ofFn]
  fin_cases a;
  fin_cases b; simp;
  exact trivial
  simp [Mathlib.Vector.ofFn];
  exact fun a ↦ a

-- example : HatPattern = (rot_cw ∘ rot_cw) HatPattern :=
--example : HatPattern = (rot_cw ∘ rot_cw ∘ rot_cw ∘ rot_cw) HatPattern := by
--  simp only [Function.comp_apply]
--  simp [rot_cw]
--  ext i j
--  fin_cases i; simp
--  fin_cases j; aesop; aesop; aesop
--  fin_cases j; aesop; aesop; aesop
--  done

--lemma vpk_eq_rot_hpk (k : ℕ): VerticalkPattern k = rot_cw (HorizontalkPattern k) := by
--  ext _ j
--  fin_cases j
--  rfl

---

@[simp] lemma avoid_le_ex {n : ℕ} {P : α → β → Prop} (M : Fin n → Fin n → Prop) (AvoidP : ¬ contains P M)
: density M ≤ ex P n :=  by
  rw [ex]
  apply le_sup
  simpa only [mem_filter, Finset.mem_univ, true_and]

--@[simp]
--theorem ex.le_sup_iff {α : Type u_2} {ι : Type u_5} [linear_order α] [order_bot α] {s : finset ι} {f : ι → α} {a : α} (ha : ⊥ < a) :
--a ≤ s.sup f ↔ ∃ (b : ι) (H : b ∈ s), a ≤ f b :=
--let  M (i j : Fin n) :  Prop := i = (0 : Fin n) ∨ j = (0 : Fin n)
--have MavI2 : ¬contains (Identity 2) M := ?proof_of_MavI2
--have Mhastwon : 2*n  ≤ density n M +1 := ?proof_of_Mhastwon-

--(ha : ⊥ < a)
@[simp] theorem le_ex_iff (P : α → β → Prop) (P_nonempty : ∃ a b, P a b ) {a n : ℕ}
: a ≤ ex P n ↔ ∃ (M : Fin n → Fin n → Prop) , ¬contains P M ∧ a ≤ density M := by
  cases a
  case zero =>  --zero is easy just take the zero matrix
    have : 0 ≤ ex P n := by simp only [zero_le]
    have : ∃ (M : Fin n → Fin n → Prop) , ¬contains P M ∧ 0 ≤ density M := by
      let M (_ _ : Fin n) :  Prop := false
      use M
      simp
      by_contra McontainP
      rw [contains] at McontainP
      obtain ⟨f,_,g,_,m⟩ := McontainP
      obtain ⟨a,b,Pab⟩ := P_nonempty
      have := m a b Pab
      have := M (f a) (g b)
      contradiction
    aesop
    done
  case succ =>
    apply Iff.intro
    · -- (→)
      intro h1
      simp [ex] at h1
      exact h1
      done
    · -- (←)
      intro ⟨M,avoids_P,has_a⟩
      rw [ex, Finset.le_sup_iff]
      use M
      aesop; aesop
      done
    done


lemma PatternOneIsIdentity : onePattern = (identityPattern 1) := by
  ext -- apply function extensionality for all a F(a) = G(a) => F = G
  simp [identityPattern, onePattern]
  exact Subsingleton.elim ..

lemma exPatternOne (n : ℕ) : ex onePattern n = 0 := by
  rw [ex]
  simp [filter_eq_empty_iff]
  intro M
  contrapose
  simp
  intro Mnonzero
  simp only [density, card_eq_zero, filter_eq_empty_iff, Finset.mem_univ, true_implies, Prod.forall, not_forall,
  not_not] at Mnonzero
  obtain ⟨i,j,Mij⟩ := Mnonzero
  simp [contains]
  refine ⟨fun _ ↦ i, by simp [StrictMono], ![j], by simp [StrictMono], by simp [Mij]⟩

example (n : ℕ) : ex (identityPattern 1) n = 0 := by
  rw [← PatternOneIsIdentity]
  exact exPatternOne n

lemma injOn_aux (n : ℕ) [NeZero n] :
    InjOn (fun z : ℤ ↦ ((↑(z⁺), ↑(z⁻)) : Fin n × Fin n)) (Set.Ioo (-n) n : Set ℤ) :=
  ((CharP.intCast_injOn_Ico _ n).prodMap (CharP.intCast_injOn_Ico _ n)).comp
    posPart_negPart_injective.injOn fun z hz ↦
    ⟨⟨posPart_nonneg _, by simpa [NeZero.pos] using hz.2⟩,
      ⟨negPart_nonneg _, by simpa [NeZero.pos] using hz.1⟩⟩

--set_option diagnostics true
lemma  exIdentity2LB  (n : ℕ )[NeZero n]: 2*n-1 ≤ ex (identityPattern 2) n  := by
  --The following code is a bad style: (a lot of unnecessary casting to deal with, e.g. double-casting)
  --let  M (i j : Fin n) :  Prop := i.val = 0  ∨ j.val = 0
  --Better to use this one:
  let  M (i j : Fin n) :  Prop := i = (0 : Fin n) ∨ j = (0 : Fin n)
  have : ¬contains (identityPattern 2) M := ?proof_of_M_avoids_I2
  have : 2*n -1 ≤ density M := ?proof_of_Mhastwon--(filter (fun x ↦ M x.1 x.2 : Fin n × Fin n → Prop) univ).card +1 := ?proof_of_Mhastwon
  -- Main proof starts here --
  rw [le_ex_iff]
  use M
  -- prove that (P is non-empty)
  case P_nonempty => simp [identityPattern]

  -- It remains to prove MavI2 and Mhastwon
  case proof_of_M_avoids_I2 =>
    by_contra h
    simp [contains] at h
    obtain ⟨ f,hf,g, hg, pmap ⟩ := h
    simp [M, identityPattern] at pmap
    simp [StrictMono] at hf hg
    have f1g0: 0 < f 1 := by
      by_contra f0
      simp at f0
      have fmono: f 0 < f 1 := by simp [hf]
      rw [f0] at fmono
      contradiction
    have g1g0: 0 < g 1 := by
      by_contra g0
      simp at g0
      have gmono: g 0 < g 1 := by simp [hg]
      rw [g0] at gmono
      contradiction
    specialize pmap 1
    cases' pmap
    aesop;aesop
  -- Now, we prove Mhastwon
  case proof_of_Mhastwon =>
    let t := (filter (fun x ↦ M x.1 x.2 : Fin n × Fin n → Prop) univ)
    simp only [density, ge_iff_le, M]
    let s : Finset ℤ := Ioo (-n ) (n)
    let f :  ℤ → Fin n × Fin n  := fun (i) ↦ (↑(i⁺) , ↑(i⁻))
    have : s = (Set.Ioo (-n) n : Set ℤ ) := by aesop
    have f_inj: InjOn f s := by simp [injOn_aux n,this]
    have hf :  ∀ a ∈ s, f a ∈ t := by
      intro a ains
      simp [s] at ains
      simp [M, t]
      obtain hha | hha' := le_total a 0
      left
      have : a⁺ = 0 := by rwa [posPart_eq_zero]
      simp [this]
      -- use ful command rw [← Fin.val_zero' n, Fin.val_inj]--, Fin.natCast_eq_zero]
      right
      have : a⁻ = 0 := by rwa [negPart_eq_zero]
      simp [this]
    have: s.card ≤ t.card:= Finset.card_le_card_of_injOn f hf f_inj
    have: s.card = 2*n -1 := by
      simp [s]
      norm_cast
      rw [Int.toNat_ofNat]
      omega
    have: 2*n -1 ≤ t.card := by aesop
    convert this



lemma exIdentity2UB (n : ℕ) : ex (identityPattern 2) n ≤ 2*n-1 := by
  classical
  rw [ex]
  simp
  intro M
  contrapose
  simp [density]
  intro M_has_two_n_points

  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i - j
  let s := (filter (fun (i, j) ↦ M i j) univ)
  have : s.card > 2*n-1 := by aesop
  let t : Finset ℤ := Icc (-n + 1) (n - 1)
  have tcardeq2nm1 : t.card = 2*n -1 := by
    simp [t]
    cases n
    · contradiction
    simp
    rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
    omega
  let k := 1

  have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]; omega

  have hn : t.card * k < s.card := by
    simp [k, s, t]
    cases n
    · contradiction
    simp
    rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
    omega

  obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
  simp only [k] at hy'
  rw [one_lt_card] at hy'
  simp only [mem_filter, ne_eq] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := hy'
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb

  have ⦃x⦄ (ha : x ∈ s) : M x.1 x.2 := by aesop
  have hmaa : M a.1 a.2 := by aesop
  have hmbb : M b.1 b.2 := by aesop
  have abneq : ¬ (a.1 = b.1 ∧ a.2 = b.2) := by aesop
  have dominance : (a.1 < b.1 ∧ a.2 < b.2) ∨ (a.1 > b.1 ∧ a.2 > b.2) := by
    rw [← ha'] at hb'
    simp only [f] at hb'
    rw [sub_eq_sub_iff_add_eq_add] at hb'
    omega
  simp [contains]

  cases dominance with
  | inl halb =>
    obtain ⟨a1leqb1, a2leqb2⟩ := halb
    let fM : Fin 2 → Fin n := ![a.1, b.1]
    let gM : Fin 2 → Fin n := ![a.2, b.2]
    have monof : StrictMono fM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [fM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a1leqb1]
    have monog : StrictMono gM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [gM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a2leqb2]

    refine ⟨fM, monof, gM, monog, by
    intro a' b' idab
    simp [identityPattern] at idab
    rw [idab]
    simp [fM, gM]
    subst b'
    fin_cases a';simp
    exact hmaa
    exact hmbb
   ⟩
  | inr hbla =>
    obtain ⟨a1leqb1, a2leqb2⟩ := hbla
    let fM : Fin 2 → Fin n := ![b.1, a.1]
    let gM : Fin 2 → Fin n := ![b.2, a.2]
    have monof : StrictMono fM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [fM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a1leqb1]
    have monog : StrictMono gM := by
      simp [StrictMono]
      intro a_fM b_fM aleqb_fM
      simp [gM]
      have abeqfm : a_fM = 0 ∧ b_fM = 1 := by omega
      obtain ⟨a_fM_eq_zero, b_fM_eq_one⟩ := abeqfm
      simp [a_fM_eq_zero, b_fM_eq_one, a2leqb2]

    refine ⟨fM, monof, gM, monog, by
      intro a' b' idab
      simp [identityPattern] at idab
      rw [idab]
      simp [fM, gM]
      subst b'
      fin_cases a';simp
      exact hmbb
      exact hmaa
    ⟩
  done

theorem exIdentity2  (n : ℕ )[NeZero n]: 2*n-1 = ex (identityPattern 2) n  :=
  Eq.symm (Nat.le_antisymm  (exIdentity2UB n)  (exIdentity2LB n))

lemma exVerticalTwoPattern (n : ℕ)  [NeZero n]  : ex VerticalTwoPattern n = n := by
  have UB: ex VerticalTwoPattern n ≤ n := ?Proof_UB
  have LB: n ≤ ex VerticalTwoPattern n := ?Proof_LB
  exact Nat.le_antisymm UB LB

  case Proof_LB =>
    let  M (i j : Fin n) : Prop := i = (0 : Fin n)
    have : ¬contains VerticalTwoPattern M := ?proof_of_M_avoids_VerticalTwoPattern
    have : n ≤ density M := ?proof_of_Mhasn
  -- Main proof starts here --
    rw [le_ex_iff]
    use M
    case P_nonempty => simp [VerticalTwoPattern]

    case proof_of_Mhasn =>
      rw [density]
      simp [M]
      let s : Finset (Fin n × Fin n) := (filter (fun x : Fin n × Fin n ↦ x.1 = 0) univ)
      let f :  ℕ → Fin n × Fin n  := fun (j) ↦ ( 0 , j)

      have f_inj : ∀ i < n, ∀ j < n, f i = f j → i = j := by
        intro i hi j hj fieqfj
        simp [f] at fieqfj

        have natCast_injOn_Fin := CharP.natCast_injOn_Iio (Fin n) n -- coercion N -> Fin n is only injective on [0, n[
        apply natCast_injOn_Fin at fieqfj; simpa;simpa;simpa
        -- Daniel Weber said that the problem is that (5 : Fin 3) = (8 : Fin 3), so you need h1 and h2 to remove the cast.
        -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Casting.20Fin.20n.20to.20Nat/near/474463179
        --apply_fun Fin.val at fieqfj
        --rwa [Fin.val_cast_of_lt hi, Fin.val_cast_of_lt hj] at fieqfj

      refine le_card_of_inj_on_range f ?_ f_inj
      intro i hi
      simp [f]

    case proof_of_M_avoids_VerticalTwoPattern =>
      by_contra cont
      rw [contains, VerticalTwoPattern] at cont
      obtain ⟨f,hf,g,hg,prop⟩ := cont
      simp [StrictMono] at hf hg
      simp at prop
      specialize prop 1
      have fmono: f 0 < f 1 := by simp [hf]
      rw [prop] at fmono
      contradiction

  case Proof_UB =>
    classical
    rw [ex]
    simp
    intro M
    contrapose
    simp [density]
    intro more_than_n

    let f : Fin n × Fin n → ℕ := fun ⟨i, j⟩ ↦ j
    let s := (filter (fun (i, j) ↦ M i j) univ)
    have : s.card > n := by aesop
    let t : Finset ℕ := Finset.Iio n
    let k := 1
    have hf ⦃a⦄ (_ : a ∈ s) : f a ∈ t := by simp [f, t]
    have hn : t.card * k < s.card := by aesop
    obtain ⟨y, hy, hy'⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hn
    simp only [k] at hy'
    rw [one_lt_card] at hy'
    simp only [mem_filter, ne_eq] at hy'
    obtain ⟨a, ha, b, hb, hab⟩ := hy'
    obtain ⟨ha, ha'⟩ := ha
    obtain ⟨hb, hb'⟩ := hb
    rw [contains]
    have: a.2 = b.2 := by
      simp [f] at ha' hb'
      rw [← ha'] at hb'
      omega

    have dominance : (a.1 < b.1) ∨ (b.1 < a.1) := by
      have: a.1 ≠ b.1 := ?_
      aesop
      by_contra a1b1
      apply hab
      aesop

    let g := ![a.2]
    have gmono : StrictMono g := by simp [StrictMono]

    cases dominance with
    | inl ab =>
      let f := ![a.1, b.1]
      have fmono : StrictMono f := by
        simp [f, StrictMono]
        intro i j hij
        have abeqfm : i = 0 ∧ j = 1 := by omega
        obtain ⟨hi', hj'⟩ := abeqfm
        simp [hi', hj', ab]

      refine⟨f,fmono,g,gmono, ?_⟩
      simp [VerticalTwoPattern]
      intro a b
      fin_cases a;aesop;aesop
    | inr ba =>
      let f := ![b.1, a.1]
      have fmono : StrictMono f := by
        simp [f, StrictMono]
        intro i j hij
        have abeqfm : i = 0 ∧ j = 1 := by omega
        obtain ⟨hi', hj'⟩ := abeqfm
        simp [hi', hj', ba]
      refine⟨f,fmono,g,gmono, ?_⟩
      simp [VerticalTwoPattern]
      intro a b
      fin_cases a;aesop;aesop

--lemma rotationInvariant (P : α → β → Prop) := ex P n = ex rotate(P) n := by sorry
--#eval sup {j | false} id
theorem split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred: Fin n → Fin n → Prop) :
let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
density M = density M1 + density M2 := by
  classical
  let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
  let s1 : Finset (Fin n × Fin n) := {(i,j) | M1 i j}
  let s2 : Finset (Fin n × Fin n) := {(i,j) | M2 i j}
  let s  : Finset (Fin n × Fin n) := {(i,j) | M  i j}
  have seqs1s2: s = s1 ∪ s2 := by
    ext x
    constructor
    · -- (->)
      intro xins
      simp [s] at xins
      simp [s1,s2,M1,M2]
      tauto
    · -- (<-)
      intro xins1s2
      simp [s1,s2,M1,M2] at xins1s2
      simp [s]
      tauto
  have dm : density M = s.card := by simp [density]
  have dm1: density M1 = s1.card := by
    simp [density]
    convert rfl
  have dm2: density M2 = s2.card := by --
    simp [density,M2,s2,M1]
    convert rfl
  have s1eqs2card: (s1 ∪ s2).card = s1.card + s2.card := by
    apply card_union_of_disjoint
    simp [Disjoint]
    intro x h1 h2
    intro p hp
    simp only [Finset.not_mem_empty]
    have pins1 : p ∈ s1 := by
      apply h1
      exact hp
    have pins2: p ∈ s2 := by
      apply h2
      exact hp
    simp [M1,s1] at pins1
    simp [M2,s2] at pins2
    have:= pins1.right
    have:= pins2.right
    contradiction
  rw [← seqs1s2] at s1eqs2card
  aesop


--open scoped Classical in noncomputable
theorem split_density_to_rows {n:ℕ} (M : Fin n → Fin n → Prop) : density M = ∑ i,  row_density M i := by
  classical
  let s : Finset (Fin n × Fin n) := { (x,y)| M x y}
  let f : Fin n × Fin n → Fin n  := fun x ↦ x.1
  let t : Finset (Fin n) := Finset.univ
  have H : ∀ x ∈ s, f x ∈ t := by
    intro x _
    simp [f,t]
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  simp [f,t] at h_sum_card
  have: s.card = density M := by simp [s,density]
  rw [this] at h_sum_card
  have: ∀ k, (filter (fun x ↦ f x = k) s).card = row_density M k := ?proof_fiber_row_density
  simp only [this] at h_sum_card
  exact h_sum_card

  case proof_fiber_row_density =>
    intro k
    simp [row_density]
    apply Finset.card_bij (fun (a:Fin n × Fin n)  _ ↦ a.2 ) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    -- 30 lines --> 1 lines using apply (and lean will figure out what is needed.)

    /-let s := filter (fun x_1 ↦ x_1.1 = k) {(x,y)| M x y}
    let t := filter (fun j ↦ M k j) Finset.univ
    let i : (a :Fin n × Fin n) → a ∈ s → Fin n := fun a h ↦ a.2
    let hi : ∀ (a : Fin n × Fin n) (ha : a ∈ s), i a ha ∈ t := by
      intro a ha
      simp [i]
      simp [s] at ha
      refine mem_filter.mpr ?_
      constructor
      simp
      rw [ha.2] at ha
      exact ha.1
    let i_inj : ∀ (a₁ : Fin n × Fin n) (ha₁ : a₁ ∈ s) (a₂ : Fin n × Fin n) (ha₂ : a₂ ∈ s), i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂ := by
      intro a1 ha1 a2 ha2 H
      simp [i] at H
      simp [s] at ha1 ha2
      have : a1.1 = a2.1 := by omega
      exact Prod.ext this H
    let i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b :=  by
      intro b hb
      let a := (k,b)
      let ha : a ∈ s := by
        refine mem_filter.mpr ?_
        simp [t] at hb
        simp [mem_filter]
        exact hb
      use a
      use ha
    have:= Finset.card_bij i hi i_inj i_surj
    convert this
    done-/


--  classical
  --pairwise disjoint union is too hard

theorem density_by_rows_ub {n c:ℕ}  (M : Fin n → Fin n → Prop)
(h_row_density_bounded: ∀i, row_density M i ≤ c) : density M ≤  n * c  :=  calc
    density M = ∑ i,  row_density M i := split_density_to_rows M
    _         ≤ ∑ _, c := by
              apply Finset.sum_le_sum
              simp [mem_filter]
              exact h_row_density_bounded
    _         = n*c := by simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

-- Finset.card_disjiUnion
-- open BigOperators
example (n :ℕ)  : ex Horizontal2Pattern n ≤ n := by
  classical
  simp [ex]
  intro M noH2P
  let Pred_min_Ofrow := fun i j ↦ ∀ j', M i j' → j ≤ j'
  let M1 (i j : Fin n) : Prop := M i j ∧   (Pred_min_Ofrow i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred_min_Ofrow i j)

  have dm1: density M1 ≤ n:= ?proof_dm1
  have M2_avoids_trivial : ¬ contains onePattern M2 := ?proof_M2_av_trivial
  have dm2: density M2 ≤ 0 := calc
    density M2 ≤ ex onePattern n := avoid_le_ex M2 M2_avoids_trivial
    _ = 0  := exPatternOne n

  calc
    density M = density M1 + density M2 :=  split_density M Pred_min_Ofrow
    _         ≤ n + density M2      := by simp only [dm1, add_le_add_iff_right]
    _         ≤ n + 0               := by simp only [dm2, add_le_add_iff_left]
    _         ≤ n                   := by omega

  ---
  case proof_M2_av_trivial =>
    by_contra contains_one
    simp [contains] at contains_one
    obtain ⟨f,hf,g,hg,prop⟩ := contains_one
      --   M2    g(0)
      --  f(0)     1
    simp [M2] at prop
    specialize prop 0 0
    simp [onePattern, Pred_min_Ofrow] at prop
    obtain ⟨a,ha, ha2⟩ := prop.2
       --   M   a g(0)
      --  f(0)  1  1
    have : contains Horizontal2Pattern M  := by
      let g' := ![a, g 0]
      have hg' : StrictMono g' := by
        simp [StrictMono];
        intro x y hxy;
        fin_cases x <;> fin_cases y <;> all_goals (aesop)
      rw [contains]
      refine ⟨f,hf,g',hg', by
        -- show embedding of [1 1] pattern
        intro a b _
        fin_cases a ; fin_cases b <;> all_goals (aesop)
      ⟩
    contradiction
    done

  case proof_dm1 =>
    have h_row_one: ∀ i, row_density M1 i ≤ 1 := by
      intro i
      by_contra H
      simp [row_density, one_lt_card_iff] at H
      obtain ⟨a,ha,b,hb,aneqb⟩ := H
      simp [M1,Pred_min_Ofrow] at ha
      simp [M1,Pred_min_Ofrow] at hb
      have : a = b := by
        refine Fin.le_antisymm ?h1 ?h2
        · -- a ≤ b
          apply ha.2
          exact hb.1
        · -- b ≤ a
          apply hb.2
          exact ha.1
      contradiction

    have:= density_by_rows_ub M1 h_row_one; simp at this
    exact this

theorem ex_horizontal (k n: ℕ) : ex (horizontalkPattern k) n ≤ n*(k-1) := by
  classical
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intro M NoHPk
  have h_row_k: ∀ i, row_density M i ≤ k-1  := ?proof_h_row_k
  exact density_by_rows_ub M h_row_k

  case proof_h_row_k =>
    intro i
    by_contra H
    simp at H
    simp [row_density] at H
    let s : Finset (Fin n) := {j | M i j}
    have h: k ≤ s.card := by simp [s]; omega
    let g := s.orderEmbOfCardLe h
    have: contains (horizontalkPattern k) M := ?proof_HPk
    contradiction
    case proof_HPk =>
      simp [contains]
      refine ⟨![i], by simp [StrictMono],g, by simp [StrictMono, OrderEmbedding.lt_iff_lt], ?EmbedPatttern⟩
      · -- Proof of Embed Pattern
        simp [horizontalkPattern]
        intro j
        have: g j ∈ s := s.orderEmbOfCardLe_mem h j
        simp [s] at this
        exact this

theorem ex_vertical (k n : ℕ ) : ex (verticalkPattern k) n ≤ n*(k-1) := by
  classical
  have: ex (verticalkPattern k) n ≤ ex ( tranpose (verticalkPattern k)) n := ?exv

  calc
    ex (verticalkPattern k) n ≤ ex ( tranpose (verticalkPattern k))  n := this
    _                         = ex ( horizontalkPattern k )  n  := by rfl
    _                         ≤ n*(k-1) := ex_horizontal k n

  case exv =>
    simp [ex]
    intro M hM
    rw [← ex]
    let M' := tranpose M
    have hM': ¬ contains (tranpose (verticalkPattern k)) M' := by
      by_contra H
      obtain ⟨f,hf,g,hg, emb_pat_to_M'⟩ := H
      have: contains (verticalkPattern k) M := by
        refine ⟨g,hg,f,hf, by
          intro a b
          apply emb_pat_to_M'
        ⟩
      contradiction

    have dmeqdm' : density M = density M' :=  by
      apply Finset.card_bij (fun a _ ↦ (a.2,a.1)) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

    calc
      density M = density M' := dmeqdm'
      _         ≤ ex (tranpose (verticalkPattern k)) n := (avoid_le_ex M' hM')


theorem ex_hat (n : ℕ)  [NeZero n] : ex HatPattern n ≤ 3*n  := by
  classical
  simp [ex]
  intro M noHat

  let min_or_max_of_row := fun i j ↦ (∀ j', M i j' → j ≤ j') ∨ (∀ j', M i j' → j' ≤ j)
  let M1 (i j : Fin n) : Prop := M i j ∧   (min_or_max_of_row i j)
  let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (min_or_max_of_row i j)

  have M1_avoids_H3 : ¬ contains (horizontalkPattern 3) M1  := ?proof_M1_avoids_H3
  have M2_avoids_V2 : ¬ contains VerticalTwoPattern M2      := ?proof_M2_avoids_V2

  have dm1: density M1 ≤ n*2 := calc
     density M1 ≤ ex  (horizontalkPattern 3) n := avoid_le_ex M1 M1_avoids_H3
     _          ≤ n*2                          := ex_horizontal 3 n

  have dm2: density M2 ≤ n := calc
    density M2 ≤ ex VerticalTwoPattern n := avoid_le_ex M2 M2_avoids_V2
    _          = n                       := exVerticalTwoPattern  n

  calc
    density M = density M1 + density M2 := split_density M min_or_max_of_row
    _         ≤ n*2 + density M2      := by simp [dm1]
    _         ≤ n*2 + n               := by simp [dm2]
    _         ≤ 3*n                   := by omega

  --
  case proof_M1_avoids_H3 =>
    by_contra containsH3
    simp [contains] at containsH3
    obtain ⟨f,_,g,g_mono,prop⟩ :
      ∃ f, StrictMono f ∧
      ∃ g, StrictMono g ∧
      ∀ (a : Fin 1) (b : Fin 3),
        horizontalkPattern 3 a b → M1 (f a) (g b)
      := containsH3
    simp [horizontalkPattern] at prop
    -- prop:
    -- M1   g(0) g(1) g(2)
    -- f(0)  1    1    1
    simp [M1] at prop
    obtain ⟨_,h_min_max_g1⟩ : M (f 0) (g 1) ∧ min_or_max_of_row (f 0) (g 1) := prop 0 1
    -- since g(1) in M1, g(1) is either min or max
    cases h_min_max_g1 with
     | inl g1_min =>
      have: g 1 ≤ g 0 := by aesop (add simp g1_min)
      have: g 0 < g 1 := by aesop (add simp g_mono)
      omega
     | inr g1_max =>
      have: g 2 ≤ g 1 := by aesop (add simp g1_max)
      have: g 1 < g 2 := by aesop (add simp g_mono)
      omega
    done

  case proof_M2_avoids_V2 =>
    by_contra containsV2
    simp [contains] at containsV2
    obtain ⟨f,hf,g,_,v2_to_M2⟩ :
      ∃ f, StrictMono f ∧
      ∃ g, StrictMono g ∧
      ∀ (a : Fin 2) (b : Fin 1),
      VerticalTwoPattern a b → M2 (f a) (g b)
      := containsV2
    simp [VerticalTwoPattern,M2] at v2_to_M2

    -- v2_to_M2:
    -- M2  g(0)
    -- f(0) 1
    -- f(1) 1

    let i := f 1
    let j := g 0

    obtain ⟨_,h_non_min_max⟩  :=  v2_to_M2 1 0
    simp [min_or_max_of_row] at h_non_min_max
    obtain ⟨⟨a,ha1,ha2⟩,⟨b,hb1,hb2⟩⟩ : (∃ a, M i a ∧ a < j) ∧ (∃ b, M i b ∧ j < b)  := h_non_min_max

    --   M    a  j  b
    --  f(0)     1
    --   i    1     1

    let g' : Fin 3 → Fin n:= ![ a, j , b]
    have monog' : StrictMono g' := by
      simp [StrictMono]
      intro x y _
      fin_cases x <;> fin_cases y <;> simp [g'] <;> all_goals (first| contradiction | omega)

    have : contains HatPattern M  := by
      rw [contains]
      refine ⟨f,hf,g',monog', by
        intro x y _
        fin_cases x <;> fin_cases y <;> all_goals (aesop (add simp HatPattern))
      ⟩
    contradiction
    done

  /-  old long proof (it works but too long)
    have h_row_one: ∀ i, row_density M1 i ≤ 2 := by
      intro i
      by_contra H
      simp [row_density] at H
      have: ∃ u : Fin n, M1 i u ∧ ¬ (min_or_max_of_row i u) := ?proof_mid_point_exist
      simp [M1] at this
      obtain ⟨u, ⟨uinM,h1⟩ ,h2⟩ := this
      contradiction

      case proof_mid_point_exist =>
        simp [Finset.two_lt_card] at H
        obtain ⟨a,ha,b,hb,c,hc,anb,anc,bnc⟩ := H
        let s : Finset (Fin n):= {a,b,c}
        have h: s.card = 3 := by
          simp [s]
          rw [card_eq_three]
          use a,b,c
        let f := s.orderEmbOfFin h

        let x := f 0; have hx: x ∈ s := by simp [x,f]
        let y := f 1; have hy: y ∈ s := by simp [y,f]
        let z := f 2; have hz: z ∈ s := by simp [z,f]
        have: x < y ∧  y < z := by simp only [OrderEmbedding.lt_iff_lt, Fin.reduceLT, and_self, x, y, z]
        obtain ⟨xy,yz⟩ := this
        have M1ix : M1 i x := by
          simp [s] at hx
          rcases hx with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have M1iy : M1 i y :=  by
          simp [s] at hy
          rcases hy with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have M1iz : M1 i z :=  by
          simp [s] at hz
          rcases hz with h1 | h2 | h3
          · rwa [h1]
          · rwa [h2]
          · rwa [h3]
        have Mix : M i x := by
          apply M1_subset_M
          exact M1ix
        have Miz : M i z := by
          apply M1_subset_M
          exact M1iz
        -- main proof
        use y
        constructor
        · -- Proof: M1 i y
          exact M1iy
        · -- Proof: y not min nor max
          simp [min_or_max_of_row]
          constructor
          · -- Proof: y is not min
            use x
          · -- Proof: y is not max
            use z

    exact UB_density_by_rows M1 h_row_one-/

-- aesop
--set_option trace.aesop true

theorem ex_identity (k n: ℕ) [NeZero n] : ex (identityPattern k) n ≤ (2*n-1)*(k-1) := by
  classical
  simp [ex]
  intro M avoid_Ik
  by_contra! M_large_density
  simp [density] at M_large_density

  let f : Fin n × Fin n → ℤ := fun ⟨i, j⟩ ↦ i-j
  let s := (filter (fun (i, j) ↦ M i j) univ)
  let t : Finset ℤ := Icc (-n + 1) (n - 1)

  have:  ∃ p ∈ t, k-1 < (filter (fun x ↦ f x = p) s).card := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · simp [s,f,t]; omega;
    · simp [s, t]
      cases n
      · contradiction
      simp_all
      rw [← Nat.cast_add_one, ← Nat.cast_add, Int.toNat_ofNat]
      rename_i n _
      have: (n + 1 + n)  = (2 * (n + 1) - 1) := by omega
      rw [this]
      omega

  obtain ⟨p, hp, hp'⟩ := this
  let set_points_to_p : Finset (Fin n × Fin n):= (filter (fun x ↦ f x = p) s)
  let set_points_to_p_col : Finset (Fin n):= { x.2 | x ∈ set_points_to_p}

  have:  set_points_to_p.card = set_points_to_p_col.card := by
    apply Finset.card_bij (fun a  _ ↦ a.2) ?hi ?i_inj ?i_surj; aesop;aesop;aesop

  have pcardk: k ≤ set_points_to_p.card := by
    simp_arith at hp'
    simp [set_points_to_p]
    omega

  have hcol: k ≤ set_points_to_p_col.card := by omega

  let g := set_points_to_p_col.orderEmbOfCardLe hcol
  let f' : Fin k → Fin n := fun i ↦ ↑( (p : ℤ)  + ( (g i) : ℤ ))
  have mono_f: StrictMono f' := by
    simp [StrictMono]
    intro a b hb
    simp [f']
    have : g a ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol a
    simp [set_points_to_p_col] at this
    obtain ⟨a',ha' ⟩ := this
    simp [set_points_to_p,f] at ha'
    have : g b ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol b
    simp [set_points_to_p_col] at this
    obtain ⟨b',hb' ⟩ := this
    simp [set_points_to_p,f] at hb'
    nth_rewrite 1 [← ha'.2]
    nth_rewrite 1 [← hb'.2]
    simp only [Int.cast_sub, Int.cast_natCast, Fin.cast_val_eq_self, sub_add_cancel, gt_iff_lt]

    have ha'' := ha'.2
    rw [← hb'.2] at ha''
    have : (a' : ℤ) = ↑↑b' - ↑↑(g b)  + ↑↑(g a) := by omega
    have : g a < g b := by simpa [StrictMono]
    omega

  have: contains (identityPattern k) M := by
    refine ⟨f', mono_f,g, by simp [StrictMono], /- Embed Identity k to M-/ by
        intro x y H
        simp [identityPattern] at H
        rw [H]
        simp [f']
        have : g y ∈ set_points_to_p_col := set_points_to_p_col.orderEmbOfCardLe_mem hcol y
        simp [set_points_to_p_col] at this
        obtain ⟨a,ha⟩ := this
        simp [set_points_to_p,f] at ha
        obtain ⟨a1,ha1⟩ := ha
        simp [s] at a1
        rw [← ha1]
        simpa
      ⟩

  contradiction
  done

--∃ a ∈ filter (fun x ↦ f x = y) s, ∃ b ∈ filter (fun x ↦ f x = y) s, a ≠ b
theorem ex_eq_ex_rot_cw (n : ℕ) (P: α → β → Prop)  : ex P n = ex (rot_cw P) n := sorry
theorem ex_contains_le_ex (n : ℕ) (P Q: α → β → Prop) (h: contains P Q)   : ex P n ≤ ex Q n := sorry
theorem n_le_ex_non_trivial  (n : ℕ) (P: α → β → Prop) (h_non_trivial : ∃ x1 y1 x2 y2, P x1 y1 ∧ P x2 y2 ∧ (x1,y1) ≠ (x2,y2)) : n ≤ ex P n := sorry
--theorem ex_eq_ex_rot_ccw (n : ℕ) {P: α → β → Prop}  : ex P n = ex (rot_ccw P) n := sorry
--theorem ex_eq_ex_flip_up (n : ℕ) {P: α → β → Prop}  : ex P n = ex (rot_ccw P) n := sorry
--theorem ex_eq_ex_flip_side (n : ℕ) {P: α → β → Prop}  : ex P n = ex (rot_ccw P) n := sorry
theorem ex_eq_ex_tranpose (n : ℕ) (P: α → β → Prop)  : ex P n = ex (tranpose P) n := sorry

theorem ex_rev_id_eq_id (k n : ℕ ) : ex (revIdentityPattern k) n  = ex (identityPattern k) n := sorry

-- basic lemma in Marcus Tardos
--

lemma le_mul_div_add_one {n q :ℕ} (p : Fin n) (h: 0 < q): p < q * (p / q + 1) := by
  rw [Nat.left_distrib]
  rw [Nat.mul_comm]
  simp
  apply Nat.lt_div_mul_add
  trivial

--open Classical
-- Bij = sq submatrix of M i' j' where i' ∈ [q * (i-1)+1, q* i], j' ∈ [q * (j-1)+1, q * j]
--open scoped Classical in noncomputable
--def rectPtSetFinn {n: ℕ} (a₁ b₁ a₂ b₂ : Fin n) : Finset (Fin n × Fin n) := (Finset.Icc a₁ (b₁-1)) ×ˢ ((Finset.Icc a₂ (b₂-1))) --({ a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({ a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n))-- {(a,b) | (↑a ∈ Finset.Ico a₁ b₁) ∧ (↑b ∈ Finset.Ico a₂ b₂)}
def rectPtset (n a₁ b₁ a₂ b₂: ℕ) : Finset (Fin n × Fin n) :=
  ({ a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({ a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n)) -- {(a,b) | (↑a ∈ Finset.Ico a₁ b₁) ∧ (↑b ∈ Finset.Ico a₂ b₂)}

def rectPtsetSubset  {n : ℕ} (R C : Finset (Fin n)) : Finset (Fin n × Fin n) := R ×ˢ C
--  ({ a | ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({ a | ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n)) -- {(a,b) | (↑a ∈ Finset.Ico a₁ b₁) ∧ (↑b ∈ Finset.Ico a₂ b₂)}


--def rectPtsetSubset (n a₁ b₁ a₂ b₂: ℕ) (R C : Finset (Fin n)): Finset (Fin n × Fin n) :=
--  ({ a | a ∈ R ∧ ↑a ∈ Finset.Ico a₁ b₁} : Finset (Fin n)) ×ˢ ({ a | a ∈ C ∧ ↑a ∈ Finset.Ico a₂ b₂} : Finset (Fin n)) -- {(a,b) | (↑a ∈ Finset.Ico a₁ b₁) ∧ (↑b ∈ Finset.Ico a₂ b₂)}
open scoped Classical in noncomputable
def rectPtsetMatrix {n :ℕ }(M : Fin n → Fin n → Prop) (a₁ b₁ a₂ b₂: ℕ)  : Finset (Fin n × Fin n) :=
  {(a,b) | M a b ∧  (a,b) ∈ (rectPtset n a₁ b₁ a₂ b₂)}

open scoped Classical in noncomputable
def rectPtsetSubsetMatrix {n :ℕ }(M : Fin n → Fin n → Prop)  (R C : Finset (Fin n))  : Finset (Fin n × Fin n) :=
  {(a,b) | M a b ∧  (a,b) ∈ rectPtsetSubset R C}


-- lemma card_rectPtSetSubset {n : ℕ} (R C : Finset (Fin n)) (h: b₁ ≤ n ∧ b₂ ≤ n): (rectPtsetSubset n a₁ b₁ a₂ b₂ R C).card =  R.card * C.card := by sorry
def rectPtsetq (n q i j :ℕ) := rectPtset n (q * i) (q * (i+1)) (q * j) (q * (j+1)) --Finset (Fin n × Fin n) := ({ a | ↑a ∈ Finset.Ico (q * i) (q * (i+1))} : Finset (Fin n)) ×ˢ ({ a | ↑a ∈ Finset.Ico (q * j) (q * (j+1))} : Finset (Fin n))-- {(a,b) | (↑a ∈ Finset.Ico a₁ b₁) ∧ (↑b ∈ Finset.Ico a₂ b₂)}
open scoped Classical in noncomputable
def rectPtsetqMatrix {n:ℕ }(M : Fin n → Fin n → Prop) (q i j :ℕ) : Finset (Fin n × Fin n) :=  {(a,b) | M a b ∧  (a,b) ∈  rectPtsetq n q i j}

lemma card_rectPtSet (n a₁ b₁ a₂ b₂: ℕ) (h: b₁ ≤ n ∧ b₂ ≤ n): (rectPtset n a₁ b₁ a₂ b₂).card =  (b₁ -a₁ )*(b₂ - a₂) := by
  simp only [rectPtset, card_product]
  suffices claim: ∀x y,  y ≤ n → (filter (fun a : Fin n ↦ ↑a ∈ Finset.Ico x y) Finset.univ).card = (Finset.Ico x y).card by aesop
  -- proof of the claim
  intro x y hy
  apply Finset.card_bij (fun (a: Fin n)  _ ↦ ↑a) ?hi ?i_inj ?i_surj;aesop;aesop
  · -- ?i_surj
    intro b hb
    simp at hb
    have: b < n := by omega
    use ⟨b,this⟩
    simp_all only [Finset.mem_Ico, mem_filter, Finset.mem_univ, and_self, exists_const]

--    ({ c | ∃ r, (r,c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n))
lemma card_rectPtSetSubset {n : ℕ} (R C : Finset (Fin n)) : (rectPtsetSubset R C).card =  R.card*C.card := by simp only [rectPtsetSubset, card_product]

lemma card_rectPtsetSubsetMatrix  {n :ℕ }(M : Fin n → Fin n → Prop) (R C : Finset (Fin n)) : (rectPtsetSubsetMatrix M R C).card ≤ R.card * C.card := by
  suffices claim: (rectPtsetSubsetMatrix M R C).card ≤  (rectPtsetSubset R C).card by calc
    (rectPtsetSubsetMatrix M R C).card ≤ (rectPtsetSubset R C).card := claim
    _                               =   R.card*C.card := card_rectPtSetSubset R C
  refine Finset.card_le_card ?_
  simp only [rectPtsetSubsetMatrix, rectPtsetSubset, Prod.mk.eta, mem_product]
  intro a ha
  aesop


lemma card_rectPtsetq (n q i j : ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q) : (rectPtsetq n q i j).card =  q*q := by
  simp [rectPtsetq]
  have:= card_rectPtSet n (q * i) (q * (i+1)) (q * j) (q * (j+1)) ?_
  convert this
  exact Nat.eq_sub_of_add_eq' rfl
  exact Nat.eq_sub_of_add_eq' rfl
  obtain ⟨hi,hj⟩ := h
  constructor
  calc
    q*(i+1) ≤  q*(n/q) := Nat.mul_le_mul_left q hi
    _       = n        := Nat.mul_div_cancel' hq
  calc
    q*(j+1) ≤  q*(n/q) := Nat.mul_le_mul_left q hj
    _       = n        := Nat.mul_div_cancel' hq

--lemma card_rectPtsetq_subset (n q i j : ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q) : (rectPtsetq n q i j).card =  q*q := sorry

lemma card_rectPtsetqMatrix {n q:ℕ }(M : Fin n → Fin n → Prop) (i j :ℕ) (hq: q ∣ n) (h: i < n/q ∧ j < n/q):
  (rectPtsetqMatrix M q i j).card ≤ q*q := by

  suffices claim: (rectPtsetqMatrix M q i j).card ≤ (rectPtsetq n q i j).card by calc
    (rectPtsetqMatrix M q i j).card ≤ (rectPtsetq n q i j).card := claim
    _                               =  q* q := card_rectPtsetq n q i j hq h
  -- proof of the claim
  refine Finset.card_le_card ?_
  simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta]
  intro p h
  simp at h
  exact h.2

def blkMatrix {n : ℕ} (M : Fin n → Fin n → Prop)  (q : ℕ ) : Fin (n/q) → Fin (n/q) → Prop :=
  fun i j ↦
  ∃ p : Fin n × Fin n, M p.1 p.2  ∧ p ∈ rectPtsetq n q i j--rectPtset n (q * i) (q * (i+1)) (q * j) (q * (j+1))
  --(↑p.1,↑p.2) ∈ {(a,b) | (a ∈ Finset.Ico (q * i) (q * (i+1)))  ∧ (b ∈ Finset.Ico (q * j) (q * (j+1)))}
  --↑p.1 ∈ Finset.Ico (q * i) (q * (i+1)) ∧ ↑p.2 ∈  Finset.Ico (q * j) (q * (j+1))
  -- q * i ≤  ↑p.1 ∧ ↑p.1 < q * (i+1) ∧   q * j ≤ ↑p.2 ∧ ↑p.2 < q * (j+1)  --M p.1 p.2  ∧ ↑p.1 ∈ Finset.Icc (q*i) (q* (i+1)-1) ∧ ↑p.2 ∈ Finset.Icc (q *j) (q * (j+1)-1)
                        --↑p.1 ≥ q * i ∧ ↑p.1 ≤ q * (i+1)-1 ∧   ↑p.2 ≥ q * j ∧ ↑p.2 ≤ q * (j+1)-1

--def block_uncontract_all_one   {n : ℕ} (q : ℕ)  (M : Fin (n/q) → Fin (n/q) → Prop)  : Fin (n) → Fin (n) → Prop :=
--  fun i j ↦
--  ∃ p : Fin (n/q) × Fin (n/q),   M p.1 p.2  ∧ p.1 = (i : ℕ )/q ∧ p.2 = (j : ℕ )/q

  -- ↑i  ∈ Finset.Icc (q * (p.1-1)+1) (q* p.1) ∧ ↑j ∈ Finset.Icc (q * (p.2-1)+1) (q * j)

--def block_uncontract_all_one   {n : ℕ} (M : Fin n → Fin n → Prop) (q : ℕ)   : Fin (n*q) → Fin (n*q) → Prop :=
--  fun i j ↦
--  ∃ p : Fin n × Fin n,   M p.1 p.2  ∧ ↑p.1 ∈ Finset.Icc (q * (i-1)+1) (q* i) ∧ ↑p.2 ∈ Finset.Icc (q * (j-1)+1) (q * j)
--

open scoped Classical in noncomputable
def blk_den {n q:ℕ } (M : Fin n → Fin n → Prop) (i j : Fin (n/q)):
  ℕ :=  (rectPtsetqMatrix M q i j).card--(rectPtsetMatrix M (q * i) (q * (i+1)) (q * j) (q * (j+1))).card

#check card_eq_sum_card_fiberwise
#check le_mul_div_add_one

@[simp] lemma p_to_pq{n:ℕ} {p : Fin n × Fin n} {q : ℕ} [NeZero q]:
p ∈ rectPtset n (q * (↑p.1 / q)) (q * (↑p.1 / q + 1)) (q * (↑p.2 / q)) (q * (↑p.2 / q + 1)) := by
  simp only [rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and]
  have hq: 0 < q := by simp only [non_zero]
  refine ⟨⟨?_1a, ?_1b⟩ ,⟨?_2a,?_2b⟩⟩
  · exact Nat.mul_div_le (↑p.1) q
  · exact le_mul_div_add_one p.1 hq
  · exact Nat.mul_div_le (↑p.2) q
  · exact le_mul_div_add_one p.2 hq

open scoped Classical
theorem den_eq_sum_blk_den {n:ℕ} (M : Fin n → Fin n → Prop) (q : ℕ ) [NeZero q] (h_q_div_n: q ∣ n) :
let B := blkMatrix M q;
density M = ∑ ⟨i,j⟩ : Fin (n/q) × Fin (n/q) with B i j, blk_den M i j := by
  let B := blkMatrix M q
  let Q := Fin (n/q) × Fin (n/q)
  let N := Fin n × Fin n
  let fq : Fin n → Fin (n/q) := fun x ↦  ⟨x/q, by apply Nat.div_lt_div_of_lt_of_dvd h_q_div_n; exact x.isLt ⟩
  let s : Finset N := { (x,y)| M x y}
  let f : N → Q  := fun (i,j) ↦ (fq i, fq j)
  let t : Finset Q := {(i,j)| B i j}
  have H : ∀ x ∈ s, f x ∈ t := by
    intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [mem_filter, Finset.mem_univ, true_and, t,B,blkMatrix]
    use p
    refine ⟨hp, p_to_pq⟩
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  suffices claim: ∀ k, (filter (fun x ↦ f x = k) s).card = blk_den M k.1 k.2 by aesop
  -- proof of the last claim
  intro k
  dsimp [blk_den,rectPtsetMatrix]
  apply Finset.card_bij (fun (p:Fin n × Fin n)  _ ↦ p ) ?hi ?i_inj ?i_surj
  · -- hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t
    intro p hp
    simp only [mem_filter, Finset.mem_univ, true_and, s] at hp
    simp only [rectPtsetqMatrix, rectPtsetq, Prod.mk.eta, mem_filter, Finset.mem_univ, true_and]
    aesop
  · -- i_inj
    aesop
  · -- i_surj : ∀ b ∈ t, ∃ a, ∃ (ha : a ∈ s), i a ha = b
    intro p hp
    simp only [Prod.mk.eta, mem_filter, Finset.mem_univ, true_and,rectPtsetqMatrix, rectPtsetq] at hp
    simp only [mem_filter, Finset.mem_univ, true_and, exists_prop, exists_eq_right, s,fq]
    refine ⟨hp.1, ?_⟩
    replace hp := hp.2
    simp [rectPtset] at hp
    obtain ⟨⟨p1l,p1h⟩,p2l,p2h⟩ := hp
    simp [f,fq]
    refine Prod.ext ?i_surj.intro.intro.intro.fst ?i_surj.intro.intro.intro.snd
    · -- proving k.1
      simp
      have:  ↑p.1 / q = k.1 := by apply Nat.div_eq_of_lt_le; rwa [mul_comm];rwa [mul_comm]
      aesop
    · -- proving k.2
      simp
      have:  ↑p.2 / q = k.2 := by apply Nat.div_eq_of_lt_le;rwa [mul_comm];rwa [mul_comm]
      aesop
  done

theorem sum_blk_den_le_mul_den_blk {n q c:ℕ} (M : Fin n → Fin n → Prop) (B : Fin (n/q) → Fin (n/q) → Prop) (h: ∀ i j : Fin (n/q), B i j → blk_den M i j ≤ c):
--let B := blkMatrix M q;
∑ ⟨i,j⟩ : Fin (n/q) × Fin (n/q) with B i j, (blk_den M i j) ≤ c* density B := by
--  let  B := blkMatrix M q
  let  Q := Fin (n/q) × Fin (n/q)
  calc
    ∑ ⟨i,j⟩ : Q with B i j, blk_den M i j ≤ ∑ ⟨i,j⟩ : Q with B i j, c := by apply Finset.sum_le_sum;intros p hp; aesop
    _                                     = ({ (i,j) | B i j }: Finset Q).card*c := by exact sum_const_nat fun x ↦ congrFun rfl
    _                                     = c* density B := by apply Nat.mul_comm
  done

  --∑ x ∈ filter (fun x ↦ blkMatrix M q x.1 x.2) Finset.univ, blk_den M x.1 x.2 ≤ ∑ x ∈ filter (fun x ↦ blkMatrix M q x.1 x.2) Finset.univ, c := by
  -- _ = c* density (blkMatrix M q)  := by sorry


/-- classical
  let s : Finset (Fin n × Fin n) := { (x,y)| M x y}
  let f : Fin n × Fin n → Fin n  := fun x ↦ x.1
  let t : Finset (Fin n) := Finset.univ
  have H : ∀ x ∈ s, f x ∈ t := by
    intro x _
    simp [f,t]
  have h_sum_card:= Finset.card_eq_sum_card_fiberwise H
  simp [f,t] at h_sum_card
  observe: s.card = density M
  rw [this] at h_sum_card
  have: ∀ k, (filter (fun x ↦ f x = k) s).card = row_density M k := ?proof_fiber_row_density
  simp only [this] at h_sum_card
  exact h_sum_card

  case proof_fiber_row_density =>
    intro k
    simp [row_density]
    apply Finset.card_bij (fun (a:Fin n × Fin n)  _ ↦ a.2 ) ?hi ?i_inj ?i_surj; aesop;aesop;aesop--/


lemma av_perm_contract_av_perm {n k: ℕ} (q :ℕ) (σ : Perm (Fin k)) (M : Fin n → Fin n → Prop)
      (hM: ¬ contains (permPattern σ) M) : ¬ contains (permPattern σ) (blkMatrix M q)  := by
  by_contra H
  simp [contains] at H
  obtain ⟨f,hf,g,hg, h⟩ := H
  simp only [blkMatrix, Finset.mem_Icc] at h
  simp only [permPattern, PEquiv.toMatrix_apply, toPEquiv, PEquiv.coe_mk, Function.comp_apply,
    Option.mem_def, Option.some.injEq, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not,
     forall_eq'] at h

  --      . . g (σ i) . .
  --  .
  --  .
  -- f i         1
  --  .
  --  .
  --#check (h ).choose
  simp only [rectPtsetq, rectPtset, Finset.mem_Ico, mem_product, mem_filter, Finset.mem_univ, true_and] at h
  let f' :Fin k → Fin n:= fun i ↦ (h i).choose.1

  have f'_mono: StrictMono f' := by
    simp [StrictMono,f']
    simp [StrictMono] at hf
    intro a b hab
    have spec_a:= (h a).choose_spec
    have spec_b:= (h b).choose_spec
    obtain ⟨A,⟨B,ca_ub⟩,C,D⟩ := spec_a
    obtain ⟨E,⟨cb_lb,F⟩,G,H⟩ := spec_b
    cases q
    · simp_all
    ·
      rename_i q
      simp_all
      calc
        f' a <   (q + 1) * (↑(f a) + 1) := ca_ub
        _   ≤ (q + 1) * ↑(f b) := by
            simp_arith
            exact hf hab
        _   ≤ f' b := cb_lb

  --            . .  g (i) . .   |     . . g (σ i) . .
  --  .                          |  .
  --  .                          |  .
  -- f (σ⁻¹ i)         1         | f i         1
  --  .                          |  .
  --  .                          |  .

  let g' :Fin k → Fin n:= fun i ↦ (h (σ.invFun i)).choose.2

  have g'_mono: StrictMono g' := by
    simp [StrictMono]
    simp [StrictMono] at hg
    intro a b hab
    have spec_a:=  (h (σ.invFun a)).choose_spec
    have spec_b:=  (h (σ.invFun b)).choose_spec

    obtain ⟨A,B,C,ca_ub⟩ := spec_a
    obtain ⟨D,E,cb_lb,F⟩ := spec_b

    simp_all
    cases q
    · simp_all
    ·
      rename_i q
      calc
        g' a  <  (q + 1) * (↑(g a) + 1)  := by simp_all [g']
        _   ≤ (q + 1) * (↑(g b) )  := by
            simp_arith
            exact hg hab
        _   ≤ g' b := by simp_all [g']

  have: contains (permPattern σ) M := by
    refine ⟨f',f'_mono,g',g'_mono,
      by
      intro i j hab
      simp only [permPattern, PEquiv.toMatrix_apply, toPEquiv, PEquiv.coe_mk, Function.comp_apply,
        Option.mem_def, Option.some.injEq, ite_eq_left_iff, zero_ne_one, imp_false,
        Decidable.not_not] at hab
      subst hab
      have := Classical.choose_spec (h i)
      simp [f',g']
      simp_all only [f']
    ⟩

  contradiction
  done

-- sum super column
--
-- den_leq_den_of_submatrix
--lemma le_mul_div_add_ones {n q p:ℕ}  (h: 0 < q): p < q * (p / q + 1) := by
--   linarith
#check rectPtsetqMatrix
#check den_eq_sum_blk_den
--let B := blkMatrix M q;
--density M = ∑ ⟨i,j⟩ : Fin (n/q) × Fin (n/q) with B i j, blk_den M i j

#check sum_blk_den_le_mul_den_blk
--theorem sum_blk_den_le_mul_den_blk {n q: ℕ} (M : Fin n → Fin n → Prop) (B: Fin (n/q) → Fin (n/q) → Prop) (c: ℕ )
--(h: ∀ i j : Fin (n/q), blk_den M i j ≤ c) : ∑ ⟨i,j⟩ : Fin (n/q) × Fin (n/q) with B i j, (blk_den M i j) ≤ c* density B := sorry

#check  sum_blk_den_le_mul_den_blk
--∑ ⟨i,j⟩ : Fin (n/q) × Fin (n/q) with B i j, (blk_den M i j) ≤ c* density B

theorem split_density_blk {n q: ℕ} (M : Fin n → Fin n → Prop)  (f1 f2: Fin (n/q) → Fin (n/q) → Prop) :
  --let M' := {(a,b) : Fin n × Fin n |  M a b ∧  (a,b) ∈  rectPtsetq n q i j}
  let Q := Fin (n/q) × Fin (n/q)
  let f3 := fun i j ↦ (¬ f1 i j) ∧ ¬ (f2 i j)
  let B := blkMatrix M q
  let B1 (i j : Fin (n/q)) : Prop :=  B i j ∧ f1 i j
  let B2 (i j : Fin (n/q)) : Prop :=  B i j ∧ f2 i j
  let N  (i j : Fin (n/q)) : Prop :=  B i j ∧ f3 i j

  density M ≤ ∑ ⟨i,j⟩ : Q with B1 i j , blk_den M i j +
              ∑ ⟨i,j⟩ : Q with B2 i j , blk_den M i j +
              ∑ ⟨i,j⟩ : Q with N  i j , blk_den M i j
              := sorry

--theorem split_density {n : ℕ} (M : Fin n → Fin n → Prop) (Pred: Fin n → Fin n → Prop) :
--let M1 (i j : Fin n) : Prop := M i j ∧   (Pred i j);
--let M2 (i j : Fin n) : Prop := M i j ∧ ¬ (Pred i j);
--density M = density M1 + density M2 := by

-- huskel-like operator |>

example {k : ℕ }  [NeZero k] (σ : Perm (Fin k))  (n : ℕ) [NeZero n] (h_k_div_n: k*k ∣ n) : ex (permPattern σ) n  ≤ n*k := by
  simp only [ex, Finset.sup_le_iff, mem_filter, Finset.mem_univ, true_and]
  intros M M_avoid_perm
  let q : ℕ := k*k
  let B := blkMatrix M q
  let Q := Fin (n/q) × Fin (n/q)

  have recurrence :  ex (permPattern σ) n ≤ (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) + 2*n * k*k := by
    let W : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ c | ∃ r, (r,c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
    let T : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ({ r | ∃ c, (r,c) ∈ rectPtsetqMatrix M q i j}: Finset (Fin n)).card ≥ k
    let S : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ ¬ W i j ∧ ¬ T i j

    let WB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ W i j ∧ B i j
    let TB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ T i j ∧ B i j
    let SB : Fin (n/q) → Fin (n/q) → Prop := fun i j ↦ S i j ∧ B i j

    have sum_small_blks: ∑ ⟨i,j⟩ : Q with SB i j, blk_den M i j ≤ (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := by
      have h1: ∀ (i j : Fin (n / q)), SB i j → blk_den M i j ≤ (k-1)*(k-1) := by
        intro i j hij
        simp [blk_den]
        simp [SB,S,W,T,B, blkMatrix]   at hij
        obtain ⟨⟨num_cols,num_rows⟩,_⟩ := hij
        let R := (filter (fun r ↦ ∃ c, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
        let C := (filter (fun c ↦ ∃ r, (r, c) ∈ rectPtsetqMatrix M q ↑i ↑j) Finset.univ)
        have rc: R.card ≤ k - 1 := Nat.le_sub_one_of_lt num_rows
        have cc: C.card ≤ k - 1 := Nat.le_sub_one_of_lt num_cols
        have: (rectPtsetSubsetMatrix M R C) = rectPtsetqMatrix M q ↑i ↑j := by
          ext x
          simp only [rectPtsetSubsetMatrix, rectPtsetSubset, Prod.mk.eta, mem_product, mem_filter,
            Finset.mem_univ, true_and, rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico,
            and_congr_right_iff]
          intro hx
          simp only [rectPtsetqMatrix, rectPtsetq, rectPtset, Finset.mem_Ico, Prod.mk.eta,
            mem_product, mem_filter, Finset.mem_univ, true_and, R, C]
          aesop
        rw [← this]
        calc
          (rectPtsetSubsetMatrix M R C).card  ≤ R.card * C.card := card_rectPtsetSubsetMatrix M R C
          _                                   ≤ (k - 1) * (k - 1) := Nat.mul_le_mul rc cc

      have h2: density SB ≤ ex (permPattern σ) (n/q)  := by
        suffices ¬ contains (permPattern σ) SB from avoid_le_ex SB this
        have B_av_perm := av_perm_contract_av_perm q σ M M_avoid_perm
        by_contra!
        simp only [contains, SB] at this
        obtain ⟨f,hf,g,hg,_⟩ := this
        have : contains (permPattern σ) (blkMatrix M q):= by
          simp only [contains]
          refine ⟨f,hf,g,hg, by aesop⟩
        contradiction

      calc
        ∑ ⟨i,j⟩ : Q with SB i j, blk_den M i j ≤ (k-1)*(k-1) * density SB := by convert sum_blk_den_le_mul_den_blk M SB h1
        _                                      ≤ (k-1)*(k-1) * ex (permPattern σ) (n/q) := Nat.mul_le_mul_left ((k - 1) * (k - 1)) h2

    have sum_wide_blocks: ∑ ⟨i,j⟩ : Q with WB i j, blk_den M i j ≤ n * k*k := by
      have h1: ∀ (i j : Fin (n / q)), WB i j → blk_den M i j ≤ k*k := sorry
      have h2: density WB ≤ n  := sorry
      calc
        ∑ ⟨i,j⟩ : Q with WB i j, blk_den M i j ≤ k*k * density WB := by convert sum_blk_den_le_mul_den_blk M WB h1
        _                                      ≤ n *k *k  := sorry

    have sum_tall_blocks: ∑ ⟨i,j⟩ : Q with TB i j, blk_den M i j ≤ n * k*k := sorry

    calc
      ex (permPattern σ) n  = density M := sorry
      _                     ≤ ∑ ⟨i,j⟩ : Q with WB i j, blk_den M i j +
                              ∑ ⟨i,j⟩ : Q with TB i j, blk_den M i j +
                              ∑ ⟨i,j⟩ : Q with SB i j, blk_den M i j := ?convert_split_density_blk
      _                     ≤ ∑ ⟨i,j⟩ : Q with WB i j, blk_den M i j +
                              ∑ ⟨i,j⟩ : Q with TB i j, blk_den M i j +
                              (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := Nat.add_le_add_left sum_small_blks (∑ ⟨i,j⟩ : Q with WB i j, blk_den M i j +  ∑ ⟨i,j⟩ : Q with TB i j, blk_den M i j)
      _                     ≤ n * k*k + n * k*k + (k-1)*(k-1) * ex (permPattern σ) (n/(k*k)) := by simp only [add_le_add_iff_right]; exact Nat.add_le_add sum_wide_blocks sum_tall_blocks
      _                     = (k-1)*(k-1) * ex (permPattern σ) (n/q) + 2*n * k*k  := by ring

    case convert_split_density_blk =>
      convert split_density_blk M W T <;> all_goals (
      · rename_i x
        simp_all only [ge_iff_le, not_le, Q, q, SB, S, W, T, B, WB, TB]
        obtain ⟨fst, snd⟩ := x
        simp_all only
        apply Iff.intro
        · intro a
          simp_all only [and_self]
        · intro a
          simp_all only [and_self]
      )
    done

  sorry



--theorem ex_permutation {k : ℕ } (σ : Perm (Fin k))  (n : ℕ) [NeZero n] [NeZero k] (h_k_div_n: k*k ∣ n) : ex (permPattern σ) n  ≤ n*k := by sorry

--theorem ex_permutation {k : ℕ } (σ : Perm (Fin k))  (n : ℕ)  : ex (permPattern σ) n  ≤ n*k := sorry
