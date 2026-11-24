import LeanNanoLlvm.Util.ConcreteOrMVar
import LeanNanoLlvm.Util.IEEEFloat

namespace LeanNanoLlvm.AST

abbrev Width (φ : Nat) := ConcreteOrMVar Nat φ
abbrev Width.concrete : Nat -> Width φ := ConcreteOrMVar.concrete
abbrev Width.mvar : Fin φ -> Width φ := ConcreteOrMVar.mvar

def Width.print : Width φ → String
  | .concrete w => s!"i{w}"
  | .mvar i => s!"i${i}"

def Width.toNat? : Width φ → Option Nat
  | .concrete w => some w
  | .mvar _ => none

@[simp]
def Width.instantiate (ws : List.Vector Nat φ) : Width φ → Width 0
  | w => .concrete <| ConcreteOrMVar.instantiate ws w

@[simp]
theorem Width.toNat?_concrete (w : Nat) : Width.toNat? (.concrete w : Width φ) = some w := rfl

@[simp]
theorem Width.toNat?_mvar (i : Fin φ) : Width.toNat? (.mvar i : Width φ) = none := rfl


inductive RawId : Type where
  | name (s : String) -- Named identifiers: %arg, %val, %x
  | anonymous (n : Nat) -- Anonymous identifiers: %0, %1
deriving Repr, DecidableEq, Inhabited

deriving instance Hashable for RawId

def RawId.ToString (s : RawId) : String :=
  match s with
  | .name str => str
  | .anonymous i => s!"{i}"

instance : ToString RawId where
  toString := RawId.ToString


inductive Identifier : Type where
  | global_id (id : RawId) -- @id
  | local_id (id : RawId) -- %id
deriving Repr, DecidableEq, Inhabited

deriving instance Hashable for Identifier

abbrev LocalId := RawId
abbrev GlobalId := RawId
abbrev BlockId := RawId
abbrev FunctionId := GlobalId

inductive InstructionId
  | id (id : RawId)
  | void (n : Nat) -- unique ids for void-returning instructions (`store`, terminators, void `call`, etc.)
deriving Repr, DecidableEq, Inhabited

/-- Supported IEEE-754 floating-point types in LLVM IR. -/
inductive FloatType : Type where
  | half
  | bfloat
  | float
  | double
  | fp128
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

namespace FloatType

@[simp]
def format : FloatType → FloatFormat
  | .half   => .half
  | .bfloat => .bfloat
  | .float  => .single
  | .double => .double
  | .fp128  => .fp128

@[simp]
def bitWidth (ft : FloatType) : Nat := ft.format.totalBits

def print : FloatType → String
  | .half   => "half"
  | .bfloat => "bfloat"
  | .float  => "float"
  | .double => "double"
  | .fp128  => "fp128"

end FloatType


section

variable (φ : Nat)

mutual

inductive LlvmRetType : Type where
  | void
  | ret (type : LlvmType)
deriving Repr

inductive LlvmType : Type where
  | int (w : Width φ)
  | float (ft : FloatType)
  | ptr (addrSpace : Nat := 0)
  | vector (len : Nat) (elem : LlvmType)
  | array (len : Nat) (elem : LlvmType)
  | struct (packed : Bool) (fields : List LlvmType)
  | function (ret : LlvmRetType) (args : List LlvmType) (isVarArg : Bool := false)
deriving Repr

end

end

section TypeEq

mutual
def LlvmRetType.beq {φ : Nat} : LlvmRetType φ → LlvmRetType φ → Bool
  | .void, .void => true
  | .ret t1, .ret t2 => LlvmType.beq t1 t2
  | _, _ => false

def LlvmType.beq {φ : Nat} : LlvmType φ → LlvmType φ → Bool
  | .int w1, .int w2 => w1 == w2
  | .float f1, .float f2 => f1 == f2
  | .ptr a1, .ptr a2 => a1 == a2
  | .vector n1 e1, .vector n2 e2 => n1 == n2 && LlvmType.beq e1 e2
  | .array n1 e1, .array n2 e2 => n1 == n2 && LlvmType.beq e1 e2
  | .struct p1 fs1, .struct p2 fs2 => p1 == p2 && LlvmType.beqList fs1 fs2
  | .function r1 a1 v1, .function r2 a2 v2 =>
      v1 == v2 && LlvmRetType.beq r1 r2 && LlvmType.beqList a1 a2
  | _, _ => false

def LlvmType.beqList {φ : Nat} : List (LlvmType φ) → List (LlvmType φ) → Bool
  | [], [] => true
  | x :: xs, y :: ys => LlvmType.beq x y && LlvmType.beqList xs ys
  | _, _ => false
end

instance {φ : Nat} : BEq (LlvmType φ) := ⟨LlvmType.beq⟩
instance {φ : Nat} : BEq (LlvmRetType φ) := ⟨LlvmRetType.beq⟩

mutual
def LlvmRetType.decEq {φ : Nat} : (a b : LlvmRetType φ) → Decidable (a = b)
  | .void, .void => isTrue rfl
  | .ret t1, .ret t2 =>
    match LlvmType.decEq t1 t2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .void, .ret _ => isFalse (by intro h; cases h)
  | .ret _, .void => isFalse (by intro h; cases h)

def LlvmType.decEq {φ : Nat} : (a b : LlvmType φ) → Decidable (a = b)
  | .int w1, .int w2 =>
    if h : w1 = w2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .float f1, .float f2 =>
    if h : f1 = f2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .ptr a1, .ptr a2 =>
    if h : a1 = a2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .vector n1 e1, .vector n2 e2 =>
    if hn : n1 = n2 then
      match LlvmType.decEq e1 e2 with
      | isTrue he => isTrue (by rw [hn, he])
      | isFalse he => isFalse (by intro heq; cases heq; exact he rfl)
    else isFalse (by intro heq; cases heq; exact hn rfl)
  | .array n1 e1, .array n2 e2 =>
    if hn : n1 = n2 then
      match LlvmType.decEq e1 e2 with
      | isTrue he => isTrue (by rw [hn, he])
      | isFalse he => isFalse (by intro heq; cases heq; exact he rfl)
    else isFalse (by intro heq; cases heq; exact hn rfl)
  | .struct p1 fs1, .struct p2 fs2 =>
    if hp : p1 = p2 then
      match LlvmType.decEqList fs1 fs2 with
      | isTrue hf => isTrue (by rw [hp, hf])
      | isFalse hf => isFalse (by intro heq; cases heq; exact hf rfl)
    else isFalse (by intro heq; cases heq; exact hp rfl)
  | .function r1 a1 v1, .function r2 a2 v2 =>
    if hv : v1 = v2 then
      match LlvmRetType.decEq r1 r2, LlvmType.decEqList a1 a2 with
      | isTrue hr, isTrue ha => isTrue (by rw [hr, ha, hv])
      | isFalse hr, _ => isFalse (by intro heq; cases heq; exact hr rfl)
      | _, isFalse ha => isFalse (by intro heq; cases heq; exact ha rfl)
    else isFalse (by intro heq; cases heq; exact hv rfl)
  | .int _, .float _ | .int _, .ptr _ | .int _, .vector _ _ | .int _, .array _ _ | .int _, .struct _ _ | .int _, .function _ _ _
  | .float _, .int _ | .float _, .ptr _ | .float _, .vector _ _ | .float _, .array _ _ | .float _, .struct _ _ | .float _, .function _ _ _
  | .ptr _, .int _ | .ptr _, .float _ | .ptr _, .vector _ _ | .ptr _, .array _ _ | .ptr _, .struct _ _ | .ptr _, .function _ _ _
  | .vector _ _, .int _ | .vector _ _, .float _ | .vector _ _, .ptr _ | .vector _ _, .array _ _ | .vector _ _, .struct _ _ | .vector _ _, .function _ _ _
  | .array _ _, .int _ | .array _ _, .float _ | .array _ _, .ptr _ | .array _ _, .vector _ _ | .array _ _, .struct _ _ | .array _ _, .function _ _ _
  | .struct _ _, .int _ | .struct _ _, .float _ | .struct _ _, .ptr _ | .struct _ _, .vector _ _ | .struct _ _, .array _ _ | .struct _ _, .function _ _ _
  | .function _ _ _, .int _ | .function _ _ _, .float _ | .function _ _ _, .ptr _ | .function _ _ _, .vector _ _ | .function _ _ _, .array _ _ | .function _ _ _, .struct _ _ =>
    isFalse (by intro h; cases h)

def LlvmType.decEqList {φ : Nat} : (a b : List (LlvmType φ)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match LlvmType.decEq x y, LlvmType.decEqList xs ys with
    | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
    | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
    | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance {φ : Nat} : DecidableEq (LlvmType φ) := LlvmType.decEq
instance {φ : Nat} : DecidableEq (LlvmRetType φ) := LlvmRetType.decEq

end TypeEq

section TypeHelpers

variable {φ : Nat}

@[simp]
def LlvmRetType.isVoid? : LlvmRetType φ → Bool
  | .void => true
  | .ret _ => false

@[simp]
def LlvmRetType.asRet? : LlvmRetType φ → Option (LlvmType φ)
  | .void => none
  | .ret ty => some ty

@[simp]
def LlvmType.asInt? : LlvmType φ → Option (Width φ)
  | .int w => some w
  | _ => none

@[simp]
def LlvmType.asFloat? : LlvmType φ → Option FloatType
  | .float ft => some ft
  | _ => none

@[simp]
def LlvmType.asPtr? : LlvmType φ → Option Nat
  | .ptr addrSpace => some addrSpace
  | _ => none

@[simp]
def LlvmType.asVector? : LlvmType φ → Option (Nat × LlvmType φ)
  | .vector n elem => some (n, elem)
  | _ => none

@[simp]
def LlvmType.asArray? : LlvmType φ → Option (Nat × LlvmType φ)
  | .array n elem => some (n, elem)
  | _ => none

@[simp]
def LlvmType.asStruct? : LlvmType φ → Option (Bool × List (LlvmType φ))
  | .struct packed fields => some (packed, fields)
  | _ => none

@[simp]
def LlvmType.asFunction? : LlvmType φ → Option (LlvmRetType φ × List (LlvmType φ))
  | .function ret argTys _ => some (ret, argTys)
  | _ => none

@[simp]
def LlvmType.isScalar : LlvmType φ → Bool
  | .int _ | .float _ | .ptr _ => true
  | _ => false

@[simp]
def LlvmType.isFirstClass : LlvmType φ → Bool
  | .function .. => false
  | _ => true

@[simp]
def LlvmType.isIntOrIntVector : LlvmType φ → Bool
  | .int _ => true
  | .vector _ (.int _) => true
  | _ => false

@[simp]
def LlvmType.isFloatOrFloatVector : LlvmType φ → Bool
  | .float _ => true
  | .vector _ (.float _) => true
  | _ => false

@[simp]
def LlvmType.isPtrOrPtrVector : LlvmType φ → Bool
  | .ptr _ => true
  | .vector _ (.ptr _) => true
  | _ => false

def LlvmType.scalarType : LlvmType φ → LlvmType φ
  | .vector _ elem => elem
  | ty => ty

def LlvmType.i (w : Width φ) : LlvmType φ := .int w

abbrev LlvmType.i1 : LlvmType φ := .i 1
abbrev LlvmType.i8 : LlvmType φ := .i 8
abbrev LlvmType.i16 : LlvmType φ := .i 16
abbrev LlvmType.i32 : LlvmType φ := .i 32
abbrev LlvmType.i64 : LlvmType φ := .i 64
abbrev LlvmType.f16 : LlvmType φ := .float .half
abbrev LlvmType.bf16 : LlvmType φ := .float .bfloat
abbrev LlvmType.f32 : LlvmType φ := .float .float
abbrev LlvmType.f64 : LlvmType φ := .float .double
abbrev LlvmType.f128 : LlvmType φ := .float .fp128

abbrev TypedIdentifier (φ : Nat) := Identifier × LlvmType φ

end TypeHelpers


/-- LLVM Fast-Math Flags (FMF). -/
structure FastMathFlags : Type where
  nnan     : Bool := false
  ninf     : Bool := false
  nsz      : Bool := false
  arcp     : Bool := false
  contract : Bool := false
  afn      : Bool := false
  reassoc  : Bool := false
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

namespace FastMathFlags

def none : FastMathFlags := {}

def fast : FastMathFlags :=
  { nnan := true, ninf := true, nsz := true, arcp := true,
    contract := true, afn := true, reassoc := true }

@[simp]
def any (f : FastMathFlags) : Bool :=
  f.nnan || f.ninf || f.nsz || f.arcp || f.contract || f.afn || f.reassoc

def toStrings (f : FastMathFlags) : List String :=
  if f == fast then ["fast"]
  else
    (if f.nnan then ["nnan"] else []) ++
    (if f.ninf then ["ninf"] else []) ++
    (if f.nsz then ["nsz"] else []) ++
    (if f.arcp then ["arcp"] else []) ++
    (if f.contract then ["contract"] else []) ++
    (if f.afn then ["afn"] else []) ++
    (if f.reassoc then ["reassoc"] else [])

end FastMathFlags


inductive IntBinaryOp : Type where
  | add (nuw : Bool) (nsw : Bool)
  | sub (nuw : Bool) (nsw : Bool)
  | mul (nuw : Bool) (nsw : Bool)
  | shl (nuw : Bool) (nsw : Bool)
  | udiv (exact : Bool)
  | sdiv (exact : Bool)
  | lshr (exact : Bool)
  | ashr (exact : Bool)
  | urem
  | srem
  | and
  | or (disjoint : Bool)
  | xor
deriving Repr, DecidableEq

inductive FloatUnaryOp : Type where
  | fneg (fmf : FastMathFlags := {})
deriving Repr, DecidableEq

inductive FloatBinaryOp : Type where
  | fadd (fmf : FastMathFlags := {})
  | fsub (fmf : FastMathFlags := {})
  | fmul (fmf : FastMathFlags := {})
  | fdiv (fmf : FastMathFlags := {})
  | frem (fmf : FastMathFlags := {})
deriving Repr, DecidableEq

/-- Integer comparison predicates (`icmp`). -/
inductive ICmpPred : Type where
  | eq | ne
  | ugt | uge | ult | ule
  | sgt | sge | slt | sle
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- Floating-point comparison predicates (`fcmp`). -/
inductive FCmpPred : Type where
  | ffalse
  | oeq | ogt | oge | olt | ole | one | ord
  | ueq | ugt | uge | ult | ule | une | uno
  | ftrue
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

/-- LLVM conversion / cast opcodes. -/
inductive ConversionOp : Type where
  | trunc (nuw : Bool) (nsw : Bool)
  | zext (nneg : Bool)
  | sext
  | fptrunc (fmf : FastMathFlags := {})
  | fpext (fmf : FastMathFlags := {})
  | fptoui
  | fptosi
  | uitofp (nneg : Bool := false) (fmf : FastMathFlags := {})
  | sitofp (fmf : FastMathFlags := {})
  | ptrtoint
  | ptrtoaddr
  | inttoptr
  | bitcast
  | addrspacecast
deriving Repr, DecidableEq

/-- GEP nowrap / inbounds flags (matches `llvm::GEPNoWrapFlags`). -/
structure GEPFlags : Type where
  inbounds : Bool := false
  nusw     : Bool := false
  nuw      : Bool := false
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

namespace GEPFlags
  def none : GEPFlags := {}
  def mkInbounds : GEPFlags := { inbounds := true, nusw := true }
  def hasNUSW (f : GEPFlags) : Bool := f.inbounds || f.nusw
end GEPFlags

/-- Parameter / return value attributes affecting poison & immediate UB (matches `llubi`). -/
inductive ValueAttr (φ : Nat) : Type where
  | noundef
  | nonnull
  | align (a : Nat)
  | dereferenceable (bytes : Nat)
  | dereferenceableOrNull (bytes : Nat)
  | range (lo hi : Int)
  | nofpclass (mask : Nat)
  | byval (ty : LlvmType φ)
deriving Repr

/-- LLVM operand expressions and constants (parameterized by symbolic width arity `φ`). -/
inductive Exp (φ : Nat := 0) : Type where
  | identifier      (id : Identifier)
  | bool            (b : Bool)
  | int             (x : Int)
  | floatBits       (bits : Nat)
  | floatDec        (neg : Bool) (mantissa : Nat) (exp10 : Int)
  | null
  | zeroinitializer
  | undef           (id : RawId)
  | poison
  | array           (elems : List (LlvmType φ × Exp φ))
  | struct          (packed : Bool) (fields : List (LlvmType φ × Exp φ))
  | vector          (elems : List (LlvmType φ × Exp φ))
  | splat           (elem : LlvmType φ × Exp φ)
  | gepConst        (flags : GEPFlags) (baseTy : LlvmType φ)
                    (ptr : LlvmType φ × Exp φ) (indices : List (LlvmType φ × Exp φ))
  | convConst       (op : ConversionOp) (fromTy : LlvmType φ) (val : Exp φ) (toTy : LlvmType φ)
  | binConst        (op : IntBinaryOp) (ty : LlvmType φ) (v1 v2 : Exp φ)
deriving Repr

abbrev TypedExp (φ : Nat) := LlvmType φ × Exp φ

section

variable {φ : Nat}

/-- LLVM IR instructions (covering integer, FP, comparisons, casts, memory, aggregates, vectors, calls, phi, freeze). -/
inductive Instruction : Type where
  | intBinaryOp    (op : IntBinaryOp) (t : LlvmType φ) (v1 : Exp φ) (v2 : Exp φ)
  | floatUnaryOp   (op : FloatUnaryOp) (t : LlvmType φ) (v : Exp φ)
  | floatBinaryOp  (op : FloatBinaryOp) (t : LlvmType φ) (v1 : Exp φ) (v2 : Exp φ)
  | icmp           (samesign : Bool) (pred : ICmpPred) (t : LlvmType φ) (v1 : Exp φ) (v2 : Exp φ)
  | fcmp           (fmf : FastMathFlags) (pred : FCmpPred) (t : LlvmType φ) (v1 : Exp φ) (v2 : Exp φ)
  | conversionOp   (op : ConversionOp) (fromTy : LlvmType φ) (v : Exp φ) (toTy : LlvmType φ)
  | select         (fmf : FastMathFlags) (condTy : LlvmType φ) (cond : Exp φ)
                   (valTy : LlvmType φ) (tv : Exp φ) (fv : Exp φ)
  | phi            (ty : LlvmType φ) (fmf : FastMathFlags) (incoming : List (Exp φ × BlockId))
  | alloca         (allocTy : LlvmType φ) (numElements : Option (LlvmType φ × Exp φ))
                   (align : Option Nat) (addrSpace : Nat := 0)
  | load           (ty : LlvmType φ) (ptrTy : LlvmType φ) (ptr : Exp φ)
                   (align : Option Nat) (isVolatile : Bool := false) (noundef : Bool := false)
  | store          (valTy : LlvmType φ) (val : Exp φ) (ptrTy : LlvmType φ) (ptr : Exp φ)
                   (align : Option Nat) (isVolatile : Bool := false)
  | getelementptr  (flags : GEPFlags) (baseTy : LlvmType φ) (ptrTy : LlvmType φ)
                   (ptr : Exp φ) (indices : List (LlvmType φ × Exp φ))
  | extractvalue   (aggTy : LlvmType φ) (agg : Exp φ) (indices : List Nat)
  | insertvalue    (aggTy : LlvmType φ) (agg : Exp φ) (valTy : LlvmType φ) (val : Exp φ) (indices : List Nat)
  | extractelement (vecTy : LlvmType φ) (vec : Exp φ) (idxTy : LlvmType φ) (idx : Exp φ)
  | insertelement  (vecTy : LlvmType φ) (vec : Exp φ) (valTy : LlvmType φ) (val : Exp φ)
                   (idxTy : LlvmType φ) (idx : Exp φ)
  | shufflevector  (vecTy : LlvmType φ) (v1 : Exp φ) (v2 : Exp φ) (mask : List (Option Nat))
  | call           (retTy : LlvmRetType φ) (fmf : FastMathFlags) (callee : Exp φ)
                   (args : List (LlvmType φ × Exp φ × List (ValueAttr φ)))
                   (retAttrs : List (ValueAttr φ) := [])
  | freeze         (v : TypedExp φ)
deriving Repr

/-- LLVM IR block terminators. -/
inductive Terminator : Type where
  | retVoid
  | ret         (v : TypedExp φ)
  | br          (dest : BlockId)
  | condBr      (cond : Exp φ) (trueDest : BlockId) (falseDest : BlockId)
  | switch      (ty : LlvmType φ) (cond : Exp φ) (defaultDest : BlockId) (cases : List (Int × BlockId))
  | unreachable
deriving Repr

structure Declaration where
  name     : FunctionId
  type     : LlvmType φ
  argAttrs : List (List (ValueAttr φ)) := []
  retAttrs : List (ValueAttr φ) := []
deriving Repr

abbrev Code := List (InstructionId × @Instruction φ)

structure Block where
  id         : BlockId
  code       : @Code φ
  terminator : InstructionId × @Terminator φ
deriving Repr

structure Definition where
  prototype : @Declaration φ
  args      : List LocalId
  blocks    : List (@Block φ)
deriving Repr

/-- Convenience accessor for single-block definitions (returns entry block if non-empty). -/
@[simp]
def Definition.entryBlock? (d : @Definition φ) : Option (@Block φ) :=
  d.blocks.head?

/-- Convenience lookup of a block by label in a definition. -/
def Definition.findBlock? (d : @Definition φ) (bid : BlockId) : Option (@Block φ) :=
  d.blocks.find? (fun b => b.id == bid)

/-- Construct a single-block definition (backwards-compatible helper). -/
@[simp]
def Definition.mkSingle (prototype : @Declaration φ) (args : List LocalId) (body : @Block φ) : @Definition φ :=
  ⟨prototype, args, [body]⟩

structure GlobalVariable where
  name        : GlobalId
  ty          : LlvmType φ
  isConstant  : Bool := false
  initializer : Option (Exp φ) := none
  align       : Option Nat := none
  addrSpace   : Nat := 0
deriving Repr

inductive TopLevelEntity where
  | global      (gv : @GlobalVariable φ)
  | declaration (decl : @Declaration φ)
  | definition  (defn : @Definition φ)
deriving Repr

structure TopLevel (φ : Nat) where
  entities : List (@TopLevelEntity φ)
deriving Repr

end


/-! ### Width Instantiation -/

section InstantiateWidths

mutual

@[simp]
def LlvmRetType.instantiateWidths (ws : List.Vector Nat φ) : LlvmRetType φ → LlvmRetType 0
  | .void => .void
  | .ret ty => .ret <| ty.instantiateWidths ws

@[simp]
def LlvmType.instantiateWidths (ws : List.Vector Nat φ) : LlvmType φ → LlvmType 0
  | .int w => .int <| Width.instantiate ws w
  | .float ft => .float ft
  | .ptr as => .ptr as
  | .vector n elem => .vector n (elem.instantiateWidths ws)
  | .array n elem => .array n (elem.instantiateWidths ws)
  | .struct packed fields => .struct packed (LlvmType.instantiateWidthsList ws fields)
  | .function ret args isVarArg =>
      .function (ret.instantiateWidths ws) (LlvmType.instantiateWidthsList ws args) isVarArg

@[simp]
def LlvmType.instantiateWidthsList (ws : List.Vector Nat φ) : List (LlvmType φ) → List (LlvmType 0)
  | [] => []
  | t :: ts => t.instantiateWidths ws :: LlvmType.instantiateWidthsList ws ts

end

@[simp]
def ValueAttr.instantiateWidths (ws : List.Vector Nat φ) : ValueAttr φ → ValueAttr 0
  | .noundef => .noundef
  | .nonnull => .nonnull
  | .align a => .align a
  | .dereferenceable b => .dereferenceable b
  | .dereferenceableOrNull b => .dereferenceableOrNull b
  | .range lo hi => .range lo hi
  | .nofpclass m => .nofpclass m
  | .byval ty => .byval (ty.instantiateWidths ws)

mutual

@[simp]
def Exp.instantiateWidths (ws : List.Vector Nat φ) : Exp φ → Exp 0
  | .identifier id => .identifier id
  | .bool b => .bool b
  | .int x => .int x
  | .floatBits b => .floatBits b
  | .floatDec neg m e => .floatDec neg m e
  | .null => .null
  | .zeroinitializer => .zeroinitializer
  | .undef id => .undef id
  | .poison => .poison
  | .array elems => .array (Exp.instantiateWidthsTypedList ws elems)
  | .struct packed fields => .struct packed (Exp.instantiateWidthsTypedList ws fields)
  | .vector elems => .vector (Exp.instantiateWidthsTypedList ws elems)
  | .splat (ty, e) => .splat (ty.instantiateWidths ws, e.instantiateWidths ws)
  | .gepConst flags baseTy (pTy, pExp) idxs =>
      .gepConst flags (baseTy.instantiateWidths ws)
        (pTy.instantiateWidths ws, pExp.instantiateWidths ws)
        (Exp.instantiateWidthsTypedList ws idxs)
  | .convConst op fromTy v toTy =>
      .convConst op (fromTy.instantiateWidths ws) (v.instantiateWidths ws) (toTy.instantiateWidths ws)
  | .binConst op ty v1 v2 =>
      .binConst op (ty.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws)

@[simp]
def Exp.instantiateWidthsTypedList (ws : List.Vector Nat φ) :
    List (LlvmType φ × Exp φ) → List (LlvmType 0 × Exp 0)
  | [] => []
  | (ty, e) :: rest => (ty.instantiateWidths ws, e.instantiateWidths ws) :: Exp.instantiateWidthsTypedList ws rest

end

@[simp]
def TypedExp.instantiateWidths (ws : List.Vector Nat φ) : TypedExp φ → TypedExp 0
  | (ty, exp) => (ty.instantiateWidths ws, exp.instantiateWidths ws)

@[simp]
def Instruction.instantiateWidths (ws : List.Vector Nat φ) : @Instruction φ → @Instruction 0
  | .intBinaryOp op t v1 v2 =>
      .intBinaryOp op (t.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws)
  | .floatUnaryOp op t v =>
      .floatUnaryOp op (t.instantiateWidths ws) (v.instantiateWidths ws)
  | .floatBinaryOp op t v1 v2 =>
      .floatBinaryOp op (t.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws)
  | .icmp ss pred t v1 v2 =>
      .icmp ss pred (t.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws)
  | .fcmp fmf pred t v1 v2 =>
      .fcmp fmf pred (t.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws)
  | .conversionOp op fromTy v toTy =>
      .conversionOp op (fromTy.instantiateWidths ws) (v.instantiateWidths ws) (toTy.instantiateWidths ws)
  | .select fmf cTy c vTy tv fv =>
      .select fmf (cTy.instantiateWidths ws) (c.instantiateWidths ws)
        (vTy.instantiateWidths ws) (tv.instantiateWidths ws) (fv.instantiateWidths ws)
  | .phi ty fmf incoming =>
      .phi (ty.instantiateWidths ws) fmf (incoming.map fun (e, b) => (e.instantiateWidths ws, b))
  | .alloca allocTy numEl align as =>
      .alloca (allocTy.instantiateWidths ws) (numEl.map fun (t, e) => (t.instantiateWidths ws, e.instantiateWidths ws)) align as
  | .load ty ptrTy ptr align isVol noundef =>
      .load (ty.instantiateWidths ws) (ptrTy.instantiateWidths ws) (ptr.instantiateWidths ws) align isVol noundef
  | .store valTy val ptrTy ptr align isVol =>
      .store (valTy.instantiateWidths ws) (val.instantiateWidths ws)
        (ptrTy.instantiateWidths ws) (ptr.instantiateWidths ws) align isVol
  | .getelementptr flags baseTy ptrTy ptr idxs =>
      .getelementptr flags (baseTy.instantiateWidths ws) (ptrTy.instantiateWidths ws) (ptr.instantiateWidths ws)
        (idxs.map fun (t, e) => (t.instantiateWidths ws, e.instantiateWidths ws))
  | .extractvalue aggTy agg idxs =>
      .extractvalue (aggTy.instantiateWidths ws) (agg.instantiateWidths ws) idxs
  | .insertvalue aggTy agg valTy val idxs =>
      .insertvalue (aggTy.instantiateWidths ws) (agg.instantiateWidths ws)
        (valTy.instantiateWidths ws) (val.instantiateWidths ws) idxs
  | .extractelement vecTy vec idxTy idx =>
      .extractelement (vecTy.instantiateWidths ws) (vec.instantiateWidths ws)
        (idxTy.instantiateWidths ws) (idx.instantiateWidths ws)
  | .insertelement vecTy vec valTy val idxTy idx =>
      .insertelement (vecTy.instantiateWidths ws) (vec.instantiateWidths ws)
        (valTy.instantiateWidths ws) (val.instantiateWidths ws)
        (idxTy.instantiateWidths ws) (idx.instantiateWidths ws)
  | .shufflevector vecTy v1 v2 mask =>
      .shufflevector (vecTy.instantiateWidths ws) (v1.instantiateWidths ws) (v2.instantiateWidths ws) mask
  | .call retTy fmf callee args retAttrs =>
      .call (retTy.instantiateWidths ws) fmf (callee.instantiateWidths ws)
        (args.map fun (t, e, attrs) =>
          (t.instantiateWidths ws, e.instantiateWidths ws, attrs.map (ValueAttr.instantiateWidths ws)))
        (retAttrs.map (ValueAttr.instantiateWidths ws))
  | .freeze (ty, v) =>
      .freeze (ty.instantiateWidths ws, v.instantiateWidths ws)

@[simp]
def Terminator.instantiateWidths (ws : List.Vector Nat φ) : @Terminator φ → @Terminator 0
  | .retVoid => .retVoid
  | .ret tv => .ret <| tv.instantiateWidths ws
  | .br dest => .br dest
  | .condBr cond tDest fDest => .condBr (cond.instantiateWidths ws) tDest fDest
  | .switch ty cond defDest cases =>
      .switch (ty.instantiateWidths ws) (cond.instantiateWidths ws) defDest cases
  | .unreachable => .unreachable

@[simp]
def Declaration.instantiateWidths (ws : List.Vector Nat φ) : @Declaration φ → @Declaration 0
  | ⟨name, type, argAttrs, retAttrs⟩ =>
      ⟨name, type.instantiateWidths ws,
        argAttrs.map (·.map (ValueAttr.instantiateWidths ws)),
        retAttrs.map (ValueAttr.instantiateWidths ws)⟩

@[simp]
def Code.instantiateWidths (ws : List.Vector Nat φ) : @Code φ → @Code 0
  | code => code.map fun (instrId, instr) => (instrId, instr.instantiateWidths ws)

@[simp]
def Block.instantiateWidths (ws : List.Vector Nat φ) : @Block φ → @Block 0
  | ⟨id, code, terminator⟩ =>
      ⟨id, code.instantiateWidths ws, (terminator.fst, terminator.snd.instantiateWidths ws)⟩

@[simp]
def Definition.instantiateWidths (ws : List.Vector Nat φ) : @Definition φ → @Definition 0
  | ⟨prototype, args, blocks⟩ =>
      ⟨prototype.instantiateWidths ws, args, blocks.map (Block.instantiateWidths ws)⟩

@[simp]
def GlobalVariable.instantiateWidths (ws : List.Vector Nat φ) : @GlobalVariable φ → @GlobalVariable 0
  | ⟨name, ty, isConst, init?, align?, as⟩ =>
      ⟨name, ty.instantiateWidths ws, isConst, init?.map (Exp.instantiateWidths ws), align?, as⟩

@[simp]
def TopLevelEntity.instantiateWidths (ws : List.Vector Nat φ) : @TopLevelEntity φ → @TopLevelEntity 0
  | .global gv => .global <| gv.instantiateWidths ws
  | .declaration decl => .declaration <| decl.instantiateWidths ws
  | .definition defn => .definition <| defn.instantiateWidths ws

@[simp]
def TopLevel.instantiateWidths (ws : List.Vector Nat φ) : @TopLevel φ → @TopLevel 0
  | ⟨entities⟩ => ⟨entities.map (TopLevelEntity.instantiateWidths ws)⟩

end InstantiateWidths

end LeanNanoLlvm.AST
