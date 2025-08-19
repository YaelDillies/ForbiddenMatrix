import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Vector.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

open OrderDual

variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

def L'' : Fin 2 → Fin 2 → Prop :=
  ![
    ![false, true],
    ![true, true]
  ]

def A' : Fin 2 → Fin 1 → Prop :=
  ![![true], ![false]]

def B' : Fin 2 → (Fin 1) → Prop :=
  ![![false], ![true]]

def tranpose (M : α → β → Prop) : β → α → Prop := fun x y ↦ M y x
def rev_all_rows (M : α → β → Prop) : α → βᵒᵈ → Prop := fun i ↦ M i ∘ ofDual
def rot_cw (M : α → β → Prop) : β → αᵒᵈ → Prop := (rev_all_rows ∘ tranpose) M

def rev_all_rows_via_list {n : ℕ} (M : α → Fin n → Prop) : α → Fin n → Prop := fun a i ↦ M a i.rev

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


def X : (Fin 3)ᵒᵈ → Bool := ![true, false, false] ∘ ofDual
def Y : Fin 3 → Bool := ![false, false, true]

def A : Fin 1 → Fin 2 → Prop := ![![true, false]]
def B : Fin 1 → (Fin 2)ᵒᵈ → Prop := ![![true, false]∘ ofDual]
def C : Fin 1 → Fin 2 → Prop := ![![false, true]]

example : (fun i ↦ C i ∘ Fin.revOrderIso ∘ toDual) = fun i ↦ rev_all_rows A i ∘ toDual := by
  ext i j; fin_cases i; fin_cases j <;> simp [rev_all_rows, A, C, Fin.rev]

-- eample : B2 = := by
--  ext
--  simp [rev_all_rows, A, B]

--def b : (Fin 2)ᵒᵈ → Bool := ![false, true] \comp ofDual
--#eval b (toDual 0)

-- the elements of (Fin 2)ᵒᵈ are, in order, toDual 1 and toDual 0
def a : Fin 2 → Bool := ![true, false]
-- b = rev_all_rows c
def c : Fin 2 → Bool := ![false, true]
def b : (Fin 2)ᵒᵈ → Bool := ![false, true] ∘ ofDual

example : a ∘ Fin.revOrderIso = b := by
  ext x
  --have := OrderDual.toDual.surjective x
  --obtain ⟨y, h⟩ :=this
  --rw [← h]
  -- one line version of above
  obtain ⟨y, rfl⟩ := OrderDual.toDual.surjective x
  fin_cases y <;> rfl

example : a ∘ Fin.revOrderIso ∘ toDual = b ∘ toDual := by
  ext x
  fin_cases x <;> rfl


example : A = rev_all_rows_via_list C := by
  ext a b; fin_cases a; fin_cases b <;> simp [A, C, rev_all_rows_via_list]

-- example : HatPattern = (rot_cw ∘ rot_cw) HatPattern :=
--example : HatPattern = (rot_cw ∘ rot_cw ∘ rot_cw ∘ rot_cw) HatPattern := by
--  simp only [Function.comp_apply]
--  simp [rot_cw]
--  ext i j
--  fin_cases i; simp
--  fin_cases j; aesop; aesop; aesop
--  fin_cases j; aesop; aesop; aesop
--  done

--lemma vpk_eq_rot_hpk (k : ℕ) : VerticalkPattern k = rot_cw (HorizontalkPattern k) := by
--  ext _ j
--  fin_cases j
--  rfl
