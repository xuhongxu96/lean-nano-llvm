/-
Released under Apache 2.0 license as described in the LICENSE of Lean-MLIR.

https://github.com/opencompl/lean-mlir
-/

-- This file defines a generic `PoisonOr α` type.

structure PoisonOr (α : Type) where
  ofOption :: toOption : Option α
deriving DecidableEq

namespace PoisonOr

@[match_pattern] def poison : PoisonOr α := ⟨none⟩
@[match_pattern] def value : α → PoisonOr α := (⟨some ·⟩)

-- TODO: elab_as_elim
@[cases_eliminator]
def casesOn'.{u} {α : Type} {motive : PoisonOr α → Sort u}
  (a? : PoisonOr α)
  (poison : motive poison)
  (value : (a : α) → motive (value a))
  : motive a? :=
  match a? with
  | .poison => poison
  | .value a => value a

@[simp] theorem value_inj {a b : α} :
  @Eq (no_index _) (value a) (value b) ↔ a = b := by
  constructor
  . rintro ⟨⟩; rfl
  . intro h; rw [h]

theorem poison_ne_value (a : α) :
  @Ne (no_index _) poison (value a) := by
  rintro ⟨⟩

theorem value_ne_poison (a : α) :
  @Ne (no_index _) (value a) poison := by
  rintro ⟨⟩

@[simp]
theorem ite_value_value {c : Prop} [Decidable c] {a b : α} :
  (if c then value a else value b : no_index _)  = value (if c then a else b) := by
  split <;> rfl

instance [ToString α] : ToString (PoisonOr α) where
  toString
  | .poison => "poison"
  | .value a => "(value " ++ addParenHeuristic (toString a) ++ ")"

instance : Monad PoisonOr where
  pure := value
  bind := fun a f => match a with
    | poison => poison
    | value a => f a

def bind_2 (a : PoisonOr α) (b : PoisonOr β) (f : α → β → PoisonOr γ) : PoisonOr γ :=
  (a >>= fun x => b >>= f x)

section Lemmas

@[simp] theorem pure_def : pure = @value α := rfl
@[simp] theorem poison_bind : poison >>= f = poison := rfl
@[simp] theorem value_bind : value a >>= f = f a := rfl
@[simp] theorem bind_poison : a? >>= (fun _ => @poison β) = poison := by
  cases a? <;> rfl

@[simp] theorem map_poison : f <$> poison = poison := rfl
@[simp] theorem map_value : f <$> value a = value (f a) := rfl

@[simp]
theorem bind_if_then_poison_eq_ite_bind (p : Prop) [Decidable p] (x : PoisonOr α) :
  (if p then poison else x : no_index _) >>= f = if p then poison else x >>= f := by
  split <;> simp

@[simp]
theorem bind_if_else_poison_eq_ite_bind (p : Prop) [Decidable p] (x : PoisonOr α) :
  (if p then x else poison : no_index _) >>= f = if p then x >>= f else poison := by
  split <;> simp

@[simp] theorem bind_2_poison_left : bind_2 poison b? f = poison := rfl
@[simp] theorem bind_2_poison_right : bind_2 a? poison f = poison := by
  cases a? <;> simp [bind_2]
@[simp] theorem bind_2_value : bind_2 (value a) (value b) f = f a b := rfl

end Lemmas

instance : LawfulMonad PoisonOr where
  map_const := by intros; rfl
  id_map := by rintro _ (_|_) <;> rfl
  seqLeft_eq := by rintro _ _ (_|_) _ <;> rfl
  seqRight_eq := by rintro _ _ (_|_) (_|_) <;> rfl
  pure_seq := by intros; rfl
  bind_pure_comp := by intros; rfl
  bind_map := by intros; rfl
  pure_bind := by intros; rfl
  bind_assoc := by rintro _ _ _ (_|_) _ _ <;> rfl

def isPoison : PoisonOr α → Bool
  | poison => true
  | value _ => false

def getValue [Inhabited α] : PoisonOr α → α
  | poison => default
  | value a => a

section Lemmas

variable {a : α}

@[simp] theorem isPoison_poison : isPoison (@poison α) = true := rfl
@[simp] theorem isPoison_value : isPoison (value a) = false := rfl

@[simp] theorem getValue_value [Inhabited α] : (value a).getValue = a := rfl
@[simp] theorem getValue_poison [Inhabited α] : (@poison α).getValue = default := rfl

@[simp] theorem mk_some (x : α) : { toOption := some x } = PoisonOr.value x := rfl
@[simp] theorem mk_none : { toOption := @none α } = PoisonOr.poison := rfl

-- TODO: simp_denote
@[simp]
theorem toOption_getSome : (PoisonOr.value x).toOption.getD y = x := by rfl
@[simp]
theorem toOption_getNone : (PoisonOr.poison).toOption.getD y = y := by rfl

end Lemmas

end PoisonOr
