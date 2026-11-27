import LeanNanoLlvm.Util.IEEEFloat
import LeanNanoLlvm.Util.Config

namespace LeanNanoLlvm.AST

inductive RawId : Type where
  | name (s : String) -- Named identifiers: %arg, %val, %x
  | anonymous (n : Nat) -- Anonymous identifiers: %0, %1
deriving Repr, DecidableEq, Inhabited

deriving instance Hashable for RawId

def RawId.toString (s : RawId) : String :=
  match s with
  | .name str => str
  | .anonymous i => s!"{i}"

instance : ToString RawId where
  toString := RawId.toString


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
  | x86_fp80
  | fp128
  | ppc_fp128
deriving Repr, DecidableEq, Inhabited

namespace FloatType

@[simp]
def format : FloatType → FloatFormat
  | .half      => .half
  | .bfloat    => .bfloat
  | .float     => .single
  | .double    => .double
  | .x86_fp80  => .x86_fp80
  | .fp128     => .fp128
  | .ppc_fp128 => .fp128

@[simp]
def bitWidth (ft : FloatType) : Nat := ft.format.totalBits

end FloatType


mutual

inductive LlvmRetType : Type where
  | void
  | ret (type : LlvmType)
deriving Repr

inductive LlvmType : Type where
  | int (w : Nat)
  | byte (w : Nat)
  | float (ft : FloatType)
  | ptr (addrSpace : Nat := 0)
  | vector (len : Nat) (elem : LlvmType)
  | array (len : Nat) (elem : LlvmType)
  | struct (packed : Bool) (fields : List LlvmType)
  | named (name : LocalId)
  | function (ret : LlvmRetType) (args : List LlvmType) (isVarArg : Bool := false)
deriving Repr

end

section TypeEq

mutual
def LlvmRetType.beq : LlvmRetType → LlvmRetType → Bool
  | .void, .void => true
  | .ret t1, .ret t2 => LlvmType.beq t1 t2
  | _, _ => false

def LlvmType.beq : LlvmType → LlvmType → Bool
  | .int w1, .int w2 => w1 == w2
  | .byte w1, .byte w2 => w1 == w2
  | .float f1, .float f2 => f1 == f2
  | .ptr a1, .ptr a2 => a1 == a2
  | .vector n1 e1, .vector n2 e2 => n1 == n2 && LlvmType.beq e1 e2
  | .array n1 e1, .array n2 e2 => n1 == n2 && LlvmType.beq e1 e2
  | .struct p1 fs1, .struct p2 fs2 => p1 == p2 && LlvmType.beqList fs1 fs2
  | .named n1, .named n2 => n1 == n2
  | .function r1 a1 v1, .function r2 a2 v2 =>
      v1 == v2 && LlvmRetType.beq r1 r2 && LlvmType.beqList a1 a2
  | _, _ => false

def LlvmType.beqList : List LlvmType → List LlvmType → Bool
  | [], [] => true
  | x :: xs, y :: ys => LlvmType.beq x y && LlvmType.beqList xs ys
  | _, _ => false
end

instance : BEq LlvmType := ⟨LlvmType.beq⟩
instance : BEq LlvmRetType := ⟨LlvmRetType.beq⟩

mutual
def LlvmRetType.decEq : (a b : LlvmRetType) → Decidable (a = b)
  | .void, .void => isTrue rfl
  | .ret t1, .ret t2 =>
    match LlvmType.decEq t1 t2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (by intro heq; cases heq; exact h rfl)
  | .void, .ret _ => isFalse (by intro h; cases h)
  | .ret _, .void => isFalse (by intro h; cases h)

def LlvmType.decEq : (a b : LlvmType) → Decidable (a = b)
  | .int w1, .int w2 =>
    if h : w1 = w2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .byte w1, .byte w2 =>
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
  | .named n1, .named n2 =>
    if h : n1 = n2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .function r1 a1 v1, .function r2 a2 v2 =>
    if hv : v1 = v2 then
      match LlvmRetType.decEq r1 r2, LlvmType.decEqList a1 a2 with
      | isTrue hr, isTrue ha => isTrue (by rw [hr, ha, hv])
      | isFalse hr, _ => isFalse (by intro heq; cases heq; exact hr rfl)
      | _, isFalse ha => isFalse (by intro heq; cases heq; exact ha rfl)
    else isFalse (by intro heq; cases heq; exact hv rfl)
  | .int _, .byte _ | .int _, .float _ | .int _, .ptr _ | .int _, .vector _ _ | .int _, .array _ _ | .int _, .struct _ _ | .int _, .named _ | .int _, .function _ _ _
  | .byte _, .int _ | .byte _, .float _ | .byte _, .ptr _ | .byte _, .vector _ _ | .byte _, .array _ _ | .byte _, .struct _ _ | .byte _, .named _ | .byte _, .function _ _ _
  | .float _, .int _ | .float _, .byte _ | .float _, .ptr _ | .float _, .vector _ _ | .float _, .array _ _ | .float _, .struct _ _ | .float _, .named _ | .float _, .function _ _ _
  | .ptr _, .int _ | .ptr _, .byte _ | .ptr _, .float _ | .ptr _, .vector _ _ | .ptr _, .array _ _ | .ptr _, .struct _ _ | .ptr _, .named _ | .ptr _, .function _ _ _
  | .vector _ _, .int _ | .vector _ _, .byte _ | .vector _ _, .float _ | .vector _ _, .ptr _ | .vector _ _, .array _ _ | .vector _ _, .struct _ _ | .vector _ _, .named _ | .vector _ _, .function _ _ _
  | .array _ _, .int _ | .array _ _, .byte _ | .array _ _, .float _ | .array _ _, .ptr _ | .array _ _, .vector _ _ | .array _ _, .struct _ _ | .array _ _, .named _ | .array _ _, .function _ _ _
  | .struct _ _, .int _ | .struct _ _, .byte _ | .struct _ _, .float _ | .struct _ _, .ptr _ | .struct _ _, .vector _ _ | .struct _ _, .array _ _ | .struct _ _, .named _ | .struct _ _, .function _ _ _
  | .named _, .int _ | .named _, .byte _ | .named _, .float _ | .named _, .ptr _ | .named _, .vector _ _ | .named _, .array _ _ | .named _, .struct _ _ | .named _, .function _ _ _
  | .function _ _ _, .int _ | .function _ _ _, .byte _ | .function _ _ _, .float _ | .function _ _ _, .ptr _ | .function _ _ _, .vector _ _ | .function _ _ _, .array _ _ | .function _ _ _, .struct _ _ | .function _ _ _, .named _ =>
    isFalse (by intro h; cases h)

def LlvmType.decEqList : (a b : List LlvmType) → Decidable (a = b)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match LlvmType.decEq x y, LlvmType.decEqList xs ys with
    | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
    | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
    | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq LlvmType := LlvmType.decEq
instance : DecidableEq LlvmRetType := LlvmRetType.decEq
instance : Inhabited LlvmType := ⟨.int 32⟩
instance : Inhabited LlvmRetType := ⟨.void⟩

end TypeEq

section TypeHelpers

@[simp]
def LlvmRetType.isVoid? : LlvmRetType → Bool
  | .void => true
  | .ret _ => false

@[simp]
def LlvmRetType.asRet? : LlvmRetType → Option LlvmType
  | .void => none
  | .ret ty => some ty

@[simp]
def LlvmType.asInt? : LlvmType → Option Nat
  | .int w => some w
  | _ => none

@[simp]
def LlvmType.asFloat? : LlvmType → Option FloatType
  | .float ft => some ft
  | _ => none

@[simp]
def LlvmType.asPtr? : LlvmType → Option Nat
  | .ptr addrSpace => some addrSpace
  | _ => none

@[simp]
def LlvmType.asVector? : LlvmType → Option (Nat × LlvmType)
  | .vector n elem => some (n, elem)
  | _ => none

@[simp]
def LlvmType.asArray? : LlvmType → Option (Nat × LlvmType)
  | .array n elem => some (n, elem)
  | _ => none

@[simp]
def LlvmType.asStruct? : LlvmType → Option (Bool × List LlvmType)
  | .struct packed fields => some (packed, fields)
  | _ => none

@[simp]
def LlvmType.asFunction? : LlvmType → Option (LlvmRetType × List LlvmType)
  | .function ret argTys _ => some (ret, argTys)
  | _ => none

@[simp]
def LlvmType.isScalar : LlvmType → Bool
  | .int _ | .byte _ | .float _ | .ptr _ => true
  | _ => false

@[simp]
def LlvmType.isFirstClass : LlvmType → Bool
  | .function .. => false
  | _ => true

@[simp]
def LlvmType.isIntOrIntVector : LlvmType → Bool
  | .int _ => true
  | .vector _ (.int _) => true
  | _ => false

@[simp]
def LlvmType.isFloatOrFloatVector : LlvmType → Bool
  | .float _ => true
  | .vector _ (.float _) => true
  | _ => false

@[simp]
def LlvmType.isPtrOrPtrVector : LlvmType → Bool
  | .ptr _ => true
  | .vector _ (.ptr _) => true
  | _ => false

def LlvmType.scalarType : LlvmType → LlvmType
  | .vector _ elem => elem
  | ty => ty

@[simp]
def LlvmType.i (w : Nat) : LlvmType := .int w

abbrev LlvmType.i1 : LlvmType := .int 1
abbrev LlvmType.i8 : LlvmType := .int 8
abbrev LlvmType.i16 : LlvmType := .int 16
abbrev LlvmType.i32 : LlvmType := .int 32
abbrev LlvmType.i64 : LlvmType := .int 64
abbrev LlvmType.f16 : LlvmType := .float .half
abbrev LlvmType.bf16 : LlvmType := .float .bfloat
abbrev LlvmType.f32 : LlvmType := .float .float
abbrev LlvmType.f64 : LlvmType := .float .double
abbrev LlvmType.f128 : LlvmType := .float .fp128


mutual
/-- Returns `true` if `ty` is or recursively contains a `.function` type (disallowed in `undef`). -/
@[simp]
def LlvmType.hasFunction : LlvmType → Bool
  | .function .. | .named _ => true
  | .vector _ elem => elem.hasFunction
  | .array _ elem => elem.hasFunction
  | .struct _ fields => LlvmType.hasFunctionList fields
  | _ => false

@[simp]
def LlvmType.hasFunctionList : List LlvmType → Bool
  | [] => false
  | t :: ts => t.hasFunction || LlvmType.hasFunctionList ts
end

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
deriving Repr, DecidableEq, Inhabited

namespace FastMathFlags

def none : FastMathFlags := {}

def fast : FastMathFlags :=
  { nnan := true, ninf := true, nsz := true, arcp := true,
    contract := true, afn := true, reassoc := true }

@[simp]
def any (f : FastMathFlags) : Bool :=
  f.nnan || f.ninf || f.nsz || f.arcp || f.contract || f.afn || f.reassoc

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
deriving Repr, DecidableEq, Inhabited

/-- Floating-point comparison predicates (`fcmp`). -/
inductive FCmpPred : Type where
  | ffalse
  | oeq | ogt | oge | olt | ole | one | ord
  | ueq | ugt | uge | ult | ule | une | uno
  | ftrue
deriving Repr, DecidableEq, Inhabited

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
deriving Repr, DecidableEq, Inhabited

namespace GEPFlags
  def none : GEPFlags := {}
  def mkInbounds : GEPFlags := { inbounds := true, nusw := true }
  def hasNUSW (f : GEPFlags) : Bool := f.inbounds || f.nusw
end GEPFlags

/-- Parameter / return value attributes affecting poison & immediate UB (matches `llubi`). -/
inductive ValueAttr : Type where
  | noundef
  | nonnull
  | align (a : Nat)
  | dereferenceable (bytes : Nat)
  | dereferenceableOrNull (bytes : Nat)
  | range (lo hi : Int)
  | rangeList (ranges : List (Int × Int))
  | nofpclass (mask : Nat)
  | byval (ty : LlvmType)
  | sret (ty : LlvmType)
  | noalias
  | readonly
deriving Repr, DecidableEq

/-- LLVM operand expressions and constants. -/
inductive Exp : Type where
  | identifier      (id : Identifier)
  | bool            (b : Bool)
  | int             (x : Int)
  | floatBits       (bits : Nat)
  | floatDec        (neg : Bool) (mantissa : Nat) (exp10 : Int)
  | floatSpecial    (neg : Bool) (isInf : Bool) (quiet : Bool) (payload : Nat := 0)
  | blockAddress    (fn : FunctionId) (blk : BlockId)
  | null
  | zeroinitializer
  | undef
  | poison
  | array           (elems : List (LlvmType × Exp))
  | struct          (packed : Bool) (fields : List (LlvmType × Exp))
  | vector          (elems : List (LlvmType × Exp))
  | splat           (elem : LlvmType × Exp)
  | gepConst        (flags : GEPFlags) (baseTy : LlvmType)
                    (ptr : LlvmType × Exp) (indices : List (LlvmType × Exp))
  | convConst       (op : ConversionOp) (fromTy : LlvmType) (val : Exp) (toTy : LlvmType)
  | binConst        (op : IntBinaryOp) (ty : LlvmType) (v1 v2 : Exp)
  | insertElemConst (vecTy : LlvmType) (vec : Exp) (elemTy : LlvmType) (elem : Exp)
                    (idxTy : LlvmType) (idx : Exp)
  | extractElemConst (vecTy : LlvmType) (vec : Exp) (idxTy : LlvmType) (idx : Exp)
  | shuffleVecConst (vecTy : LlvmType) (v1 v2 : Exp) (mask : List (Option Nat))
deriving Repr

abbrev TypedExp := LlvmType × Exp

/-- Call-site properties that are not operands: the `tail`/`musttail` marker and the calling
convention (`""` is the default `ccc`). -/
structure CallSiteInfo where
  isTail      : Bool := false
  callingConv : String := ""
deriving Repr, DecidableEq, Inhabited

/-- The default call site (no tail marker, `ccc`). -/
def CallSiteInfo.default : CallSiteInfo := {}

/-- LLVM IR instructions (covering integer, FP, comparisons, casts, memory, aggregates, vectors, calls, phi, freeze). -/
inductive Instruction : Type where
  | intBinaryOp    (op : IntBinaryOp) (t : LlvmType) (v1 : Exp) (v2 : Exp)
  | floatUnaryOp   (op : FloatUnaryOp) (t : LlvmType) (v : Exp)
  | floatBinaryOp  (op : FloatBinaryOp) (t : LlvmType) (v1 : Exp) (v2 : Exp)
  | icmp           (samesign : Bool) (pred : ICmpPred) (t : LlvmType) (v1 : Exp) (v2 : Exp)
  | fcmp           (fmf : FastMathFlags) (pred : FCmpPred) (t : LlvmType) (v1 : Exp) (v2 : Exp)
  | conversionOp   (op : ConversionOp) (fromTy : LlvmType) (v : Exp) (toTy : LlvmType)
  | select         (fmf : FastMathFlags) (condTy : LlvmType) (cond : Exp)
                   (valTy : LlvmType) (tv : Exp) (fv : Exp)
  | phi            (ty : LlvmType) (fmf : FastMathFlags) (incoming : List (Exp × BlockId))
                   (metadata : List ValueAttr := [])
  | alloca         (allocTy : LlvmType) (numElements : Option (LlvmType × Exp))
                   (align : Option Nat) (addrSpace : Nat := 0)
  | load           (ty : LlvmType) (ptrTy : LlvmType) (ptr : Exp)
                   (align : Option Nat) (isVolatile : Bool := false) (noundef : Bool := false)
                   (metadata : List ValueAttr := [])
  | store          (valTy : LlvmType) (val : Exp) (ptrTy : LlvmType) (ptr : Exp)
                   (align : Option Nat) (isVolatile : Bool := false)
  | getelementptr  (flags : GEPFlags) (baseTy : LlvmType) (ptrTy : LlvmType)
                   (ptr : Exp) (indices : List (LlvmType × Exp))
  | extractvalue   (aggTy : LlvmType) (agg : Exp) (indices : List Nat)
  | insertvalue    (aggTy : LlvmType) (agg : Exp) (valTy : LlvmType) (val : Exp) (indices : List Nat)
  | extractelement (vecTy : LlvmType) (vec : Exp) (idxTy : LlvmType) (idx : Exp)
  | insertelement  (vecTy : LlvmType) (vec : Exp) (valTy : LlvmType) (val : Exp)
                   (idxTy : LlvmType) (idx : Exp)
  | shufflevector  (vecTy : LlvmType) (v1 : Exp) (v2 : Exp) (mask : List (Option Nat))
  | call           (retTy : LlvmRetType) (fmf : FastMathFlags) (callee : Exp)
                   (args : List (LlvmType × Exp × List ValueAttr))
                   (retAttrs : List ValueAttr := [])
                   (bundles : List (String × List (LlvmType × Exp)) := [])
                   (isNoReturn : Bool := false) (site : CallSiteInfo := {})
  | freeze         (v : TypedExp)
  | bitinsert      (baseTy : LlvmType) (base : Exp) (valTy : LlvmType) (val : Exp)
                   (offTy : LlvmType) (off : Exp)
  | bitextract     (retTy : LlvmType) (srcTy : LlvmType) (src : Exp)
                   (offTy : LlvmType) (off : Exp)
deriving Repr

/-- LLVM IR block terminators. -/
inductive Terminator : Type where
  | retVoid
  | ret         (v : TypedExp)
  | br          (dest : BlockId)
  | condBr      (cond : Exp) (trueDest : BlockId) (falseDest : BlockId)
  | switch      (ty : LlvmType) (cond : Exp) (defaultDest : BlockId) (cases : List (Int × BlockId))
  | indirectBr  (addr : Exp) (dests : List BlockId)
  | unreachable
deriving Repr

structure Declaration where
  name       : FunctionId
  type       : LlvmType
  argAttrs   : List (List ValueAttr) := []
  retAttrs   : List ValueAttr := []
  isNoReturn   : Bool := false
  isNoBuiltin  : Bool := false
  denormalMode : Option DenormalMode := none
  /-- Calling convention (`""` is the default `ccc`). -/
  callingConv  : String := ""
deriving Repr

abbrev Code := List (InstructionId × Instruction)

structure Block where
  id         : BlockId
  code       : Code
  terminator : InstructionId × Terminator
deriving Repr

structure Definition where
  prototype : Declaration
  args      : List LocalId
  blocks    : List Block
deriving Repr

/-- Convenience accessor for single-block definitions (returns entry block if non-empty). -/
@[simp]
def Definition.entryBlock? (d : Definition) : Option Block :=
  d.blocks.head?

/-- Convenience lookup of a block by label in a definition. -/
def Definition.findBlock? (d : Definition) (bid : BlockId) : Option Block :=
  d.blocks.find? (fun b => b.id == bid)

structure GlobalVariable where
  name        : GlobalId
  ty          : LlvmType
  isConstant  : Bool := false
  initializer : Option Exp := none
  align       : Option Nat := none
  addrSpace   : Nat := 0
deriving Repr

inductive TopLevelEntity where
  | typeDef     (name : LocalId) (ty : LlvmType)
  | global      (gv : GlobalVariable)
  | declaration (decl : Declaration)
  | definition  (defn : Definition)
deriving Repr

structure TopLevel where
  entities : List TopLevelEntity
deriving Repr


end LeanNanoLlvm.AST
