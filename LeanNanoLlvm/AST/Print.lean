import LeanNanoLlvm.AST.AST

namespace LeanNanoLlvm.AST

def Identifier.print : Identifier → String
  | .global_id id => s!"@{id.ToString}"
  | .local_id id => s!"%{id.ToString}"

mutual

def LlvmType.print : LlvmType φ → String
  | .int w => w.print
  | .float ft => ft.print
  | .ptr 0 => "ptr"
  | .ptr as => s!"ptr addrspace({as})"
  | .vector n elem => s!"<{n} x {elem.print}>"
  | .array n elem => s!"[{n} x {elem.print}]"
  | .struct false fields =>
      let inner := String.intercalate ", " (LlvmType.printList fields)
      "{ " ++ inner ++ " }"
  | .struct true fields =>
      let inner := String.intercalate ", " (LlvmType.printList fields)
      "<{ " ++ inner ++ " }>"
  | .function ret args isVarArg =>
      let argStrs := LlvmType.printList args ++ (if isVarArg then ["..."] else [])
      s!"{ret.print} ({String.intercalate ", " argStrs})"

def LlvmType.printList : List (LlvmType φ) → List String
  | [] => []
  | t :: ts => t.print :: LlvmType.printList ts

def LlvmRetType.print : LlvmRetType φ → String
  | .void => "void"
  | .ret t => t.print

end

def ICmpPred.print : ICmpPred → String
  | .eq  => "eq"
  | .ne  => "ne"
  | .ugt => "ugt"
  | .uge => "uge"
  | .ult => "ult"
  | .ule => "ule"
  | .sgt => "sgt"
  | .sge => "sge"
  | .slt => "slt"
  | .sle => "sle"

def FCmpPred.print : FCmpPred → String
  | .ffalse => "false"
  | .oeq    => "oeq"
  | .ogt    => "ogt"
  | .oge    => "oge"
  | .olt    => "olt"
  | .ole    => "ole"
  | .one    => "one"
  | .ord    => "ord"
  | .ueq    => "ueq"
  | .ugt    => "ugt"
  | .uge    => "uge"
  | .ult    => "ult"
  | .ule    => "ule"
  | .une    => "une"
  | .uno    => "uno"
  | .ftrue  => "true"

def GEPFlags.print (f : GEPFlags) : String :=
  let parts :=
    (if f.inbounds then ["inbounds"] else []) ++
    (if !f.inbounds && f.nusw then ["nusw"] else []) ++
    (if f.nuw then ["nuw"] else [])
  if parts.isEmpty then "" else " " ++ String.intercalate " " parts

def ValueAttr.print : ValueAttr φ → String
  | .noundef => "noundef"
  | .nonnull => "nonnull"
  | .align a => s!"align {a}"
  | .dereferenceable b => s!"dereferenceable({b})"
  | .dereferenceableOrNull b => s!"dereferenceable_or_null({b})"
  | .range lo hi => s!"range({lo}, {hi})"
  | .nofpclass m => s!"nofpclass({m})"
  | .byval ty => s!"byval({ty.print})"

def IntBinaryOp.printNameAndFlags : IntBinaryOp → String × List String
  | .add nuw nsw  => ("add",  (if nuw then ["nuw"] else []) ++ (if nsw then ["nsw"] else []))
  | .sub nuw nsw  => ("sub",  (if nuw then ["nuw"] else []) ++ (if nsw then ["nsw"] else []))
  | .mul nuw nsw  => ("mul",  (if nuw then ["nuw"] else []) ++ (if nsw then ["nsw"] else []))
  | .shl nuw nsw  => ("shl",  (if nuw then ["nuw"] else []) ++ (if nsw then ["nsw"] else []))
  | .udiv exact   => ("udiv", if exact then ["exact"] else [])
  | .sdiv exact   => ("sdiv", if exact then ["exact"] else [])
  | .lshr exact   => ("lshr", if exact then ["exact"] else [])
  | .ashr exact   => ("ashr", if exact then ["exact"] else [])
  | .urem         => ("urem", [])
  | .srem         => ("srem", [])
  | .and          => ("and",  [])
  | .or disjoint  => ("or",   if disjoint then ["disjoint"] else [])
  | .xor          => ("xor",  [])

def ConversionOp.printNameAndFlags : ConversionOp → String × List String
  | .trunc nuw nsw     => ("trunc", (if nuw then ["nuw"] else []) ++ (if nsw then ["nsw"] else []))
  | .zext nneg         => ("zext",  if nneg then ["nneg"] else [])
  | .sext              => ("sext",  [])
  | .fptrunc fmf       => ("fptrunc", fmf.toStrings)
  | .fpext fmf         => ("fpext",   fmf.toStrings)
  | .fptoui            => ("fptoui",  [])
  | .fptosi            => ("fptosi",  [])
  | .uitofp nneg fmf   => ("uitofp",  (if nneg then ["nneg"] else []) ++ fmf.toStrings)
  | .sitofp fmf        => ("sitofp",  fmf.toStrings)
  | .ptrtoint          => ("ptrtoint", [])
  | .ptrtoaddr         => ("ptrtoaddr", [])
  | .inttoptr          => ("inttoptr", [])
  | .bitcast           => ("bitcast",  [])
  | .addrspacecast     => ("addrspacecast", [])

private def formatFlags (flags : List String) : String :=
  if flags.isEmpty then "" else " " ++ String.intercalate " " flags

mutual

def Exp.print : Exp φ → String
  | .identifier id => id.print
  | .bool b => s!"{b}"
  | .int i => s!"{i}"
  | .floatBits b => s!"0x{String.ofList (Nat.toDigits 16 b)}"
  | .floatDec neg m e =>
      let sgn := if neg then "-" else ""
      if e == 0 then s!"{sgn}{m}.0" else s!"{sgn}{m}e{e}"
  | .null => "null"
  | .zeroinitializer => "zeroinitializer"
  | .undef rawid => s!"undef!{rawid}"
  | .poison => "poison"
  | .array elems =>
      "[" ++ String.intercalate ", " (Exp.printTypedList elems) ++ "]"
  | .struct false fields =>
      "{ " ++ String.intercalate ", " (Exp.printTypedList fields) ++ " }"
  | .struct true fields =>
      "<{ " ++ String.intercalate ", " (Exp.printTypedList fields) ++ " }>"
  | .vector elems =>
      "<" ++ String.intercalate ", " (Exp.printTypedList elems) ++ ">"
  | .splat (ty, e) =>
      s!"splat ({ty.print} {e.print})"
  | .gepConst flags baseTy (pTy, pExp) idxs =>
      let idxStr := String.intercalate ", " (Exp.printTypedList idxs)
      s!"getelementptr{flags.print} ({baseTy.print}, {pTy.print} {pExp.print}, {idxStr})"
  | .convConst op fromTy v toTy =>
      let (name, flags) := op.printNameAndFlags
      s!"{name}{formatFlags flags} ({fromTy.print} {v.print} to {toTy.print})"
  | .binConst op ty v1 v2 =>
      let (name, flags) := op.printNameAndFlags
      s!"{name}{formatFlags flags} ({ty.print} {v1.print}, {ty.print} {v2.print})"

def Exp.printTypedList : List (LlvmType φ × Exp φ) → List String
  | [] => []
  | (ty, e) :: rest => s!"{ty.print} {e.print}" :: Exp.printTypedList rest

end

private def printBinOp (op : String) (flags : List String) (t : LlvmType φ) (v1 v2 : Exp φ) : String :=
  s!"{op}{formatFlags flags} {t.print} {v1.print}, {v2.print}"

private def printConversionOp (op : String) (flags : List String) (fromTy : LlvmType φ) (v : Exp φ) (toTy : LlvmType φ) : String :=
  s!"{op}{formatFlags flags} {fromTy.print} {v.print} to {toTy.print}"

def Instruction.print : @Instruction φ → String
  | .intBinaryOp op t v1 v2 =>
      let (name, flags) := op.printNameAndFlags
      printBinOp name flags t v1 v2
  | .floatUnaryOp (.fneg fmf) t v =>
      s!"fneg{formatFlags fmf.toStrings} {t.print} {v.print}"
  | .floatBinaryOp op t v1 v2 =>
      let (name, fmf) := match op with
        | .fadd f => ("fadd", f)
        | .fsub f => ("fsub", f)
        | .fmul f => ("fmul", f)
        | .fdiv f => ("fdiv", f)
        | .frem f => ("frem", f)
      printBinOp name fmf.toStrings t v1 v2
  | .icmp ss pred t v1 v2 =>
      let ssStr := if ss then " samesign" else ""
      s!"icmp{ssStr} {pred.print} {t.print} {v1.print}, {v2.print}"
  | .fcmp fmf pred t v1 v2 =>
      s!"fcmp{formatFlags fmf.toStrings} {pred.print} {t.print} {v1.print}, {v2.print}"
  | .conversionOp op fromTy v toTy =>
      let (name, flags) := op.printNameAndFlags
      printConversionOp name flags fromTy v toTy
  | .select fmf cTy c vTy tv fv =>
      s!"select{formatFlags fmf.toStrings} {cTy.print} {c.print}, {vTy.print} {tv.print}, {vTy.print} {fv.print}"
  | .phi ty fmf incoming =>
      let incStr := String.intercalate ", " (incoming.map fun (e, b) => s!"[ {e.print}, %{b.ToString} ]")
      s!"phi{formatFlags fmf.toStrings} {ty.print} {incStr}"
  | .alloca allocTy numEl align as =>
      let numStr := match numEl with
        | some (t, e) => s!", {t.print} {e.print}"
        | none => ""
      let alignStr := match align with
        | some a => s!", align {a}"
        | none => ""
      let asStr := if as == 0 then "" else s!", addrspace({as})"
      s!"alloca {allocTy.print}{numStr}{alignStr}{asStr}"
  | .load ty ptrTy ptr align isVol noundef =>
      let volStr := if isVol then " volatile" else ""
      let alignStr := match align with
        | some a => s!", align {a}"
        | none => ""
      let nuStr := if noundef then ", !noundef !{}" else ""
      s!"load{volStr} {ty.print}, {ptrTy.print} {ptr.print}{alignStr}{nuStr}"
  | .store valTy val ptrTy ptr align isVol =>
      let volStr := if isVol then " volatile" else ""
      let alignStr := match align with
        | some a => s!", align {a}"
        | none => ""
      s!"store{volStr} {valTy.print} {val.print}, {ptrTy.print} {ptr.print}{alignStr}"
  | .getelementptr flags baseTy ptrTy ptr idxs =>
      let idxStrs := idxs.map fun (t, e) => s!", {t.print} {e.print}"
      s!"getelementptr{flags.print} {baseTy.print}, {ptrTy.print} {ptr.print}{String.join idxStrs}"
  | .extractvalue aggTy agg idxs =>
      let idxStr := String.intercalate ", " (idxs.map toString)
      s!"extractvalue {aggTy.print} {agg.print}, {idxStr}"
  | .insertvalue aggTy agg valTy val idxs =>
      let idxStr := String.intercalate ", " (idxs.map toString)
      s!"insertvalue {aggTy.print} {agg.print}, {valTy.print} {val.print}, {idxStr}"
  | .extractelement vecTy vec idxTy idx =>
      s!"extractelement {vecTy.print} {vec.print}, {idxTy.print} {idx.print}"
  | .insertelement vecTy vec valTy val idxTy idx =>
      s!"insertelement {vecTy.print} {vec.print}, {valTy.print} {val.print}, {idxTy.print} {idx.print}"
  | .shufflevector vecTy v1 v2 mask =>
      let maskStr := String.intercalate ", " (mask.map fun
        | some i => s!"i32 {i}"
        | none => "i32 poison")
      s!"shufflevector {vecTy.print} {v1.print}, {vecTy.print} {v2.print}, <{mask.length} x i32> <{maskStr}>"
  | .call retTy fmf callee args retAttrs =>
      let retAttrStr := formatFlags (retAttrs.map ValueAttr.print)
      let argStr := String.intercalate ", " (args.map fun (t, e, attrs) =>
        s!"{t.print}{formatFlags (attrs.map ValueAttr.print)} {e.print}")
      s!"call{formatFlags fmf.toStrings}{retAttrStr} {retTy.print} {callee.print}({argStr})"
  | .freeze ⟨ty, v⟩ =>
      s!"freeze {ty.print} {v.print}"

def Terminator.print : @Terminator φ → String
  | .retVoid => "ret void"
  | .ret ⟨ty, v⟩ => s!"ret {ty.print} {v.print}"
  | .br dest => s!"br label %{dest.ToString}"
  | .condBr cond tDest fDest => s!"br i1 {cond.print}, label %{tDest.ToString}, label %{fDest.ToString}"
  | .switch ty cond defDest cases =>
      let caseStr := String.intercalate " " (cases.map fun (v, lbl) => s!"{ty.print} {v}, label %{lbl.ToString}")
      s!"switch {ty.print} {cond.print}, label %{defDest.ToString} [ {caseStr} ]"
  | .unreachable => "unreachable"

def printInstructionWithId (id : InstructionId) (instruction : @Instruction φ ⊕ @Terminator φ) : String :=
  let instructionStr := match instruction with
    | .inl instruction => instruction.print
    | .inr terminator => terminator.print

  match id with
  | .id id =>
    let id := Identifier.local_id id
    s!"{id.print} = {instructionStr}"
  | .void _ =>
    s!"{instructionStr}"

private def indentString (indent : Nat) (s : String) : String :=
  match indent with
  | 0 => ""
  | n + 1 => s ++ indentString n s

def printCode (indent : Nat) : @Code φ → String
  | .nil => ""
  | .cons ⟨id, instruction⟩ tail =>
    indentString indent " " ++ printInstructionWithId id (.inl instruction) ++ "\n" ++ printCode indent tail

def Block.print (block : @Block φ) : String :=
  let indentSize := 2
  s!"{block.id.ToString}:\n"
  ++ printCode indentSize block.code
  ++ indentString indentSize " " ++ printInstructionWithId block.terminator.fst (.inr block.terminator.snd) ++ "\n"

def Declaration.printSignature (decl : @Declaration φ) : String :=
  let id := Identifier.global_id decl.name
  match decl.type with
  | .function ret args isVarArg =>
    let argStrs := args.map (fun ty => ty.print) ++ (if isVarArg then ["..."] else [])
    let argStr := String.intercalate ", " argStrs
    s!"{ret.print} {id.print}({argStr})"
  | _ => s!"<invalid-fn-type> {id.print}()"

def Definition.printSignature (definition : @Definition φ) : String :=
  let decl := definition.prototype
  let id := Identifier.global_id decl.name
  match decl.type with
  | .function ret args isVarArg =>
    let argPairs := args.zip (definition.args.map (Identifier.local_id ·))
    let argStrs := argPairs.map (fun ⟨ty, arg⟩ => s!"{ty.print} {arg.print}") ++
      (if isVarArg then ["..."] else [])
    let argStr := String.intercalate ", " argStrs
    s!"{ret.print} {id.print}({argStr})"
  | _ => s!"<invalid-fn-type> {id.print}()"

def Declaration.print (decl : @Declaration φ) : String :=
  s!"declare {decl.printSignature}"

def Definition.print (definition : @Definition φ) : String :=
  let sig := definition.printSignature
  let blocksStr := String.join (definition.blocks.map Block.print)
  s!"define {sig} " ++ "{\n" ++ blocksStr ++ "}"

def GlobalVariable.print (gv : @GlobalVariable φ) : String :=
  let kind := if gv.isConstant then "constant" else "global"
  let asStr := if gv.addrSpace == 0 then "" else s!"addrspace({gv.addrSpace}) "
  let initStr := match gv.initializer with
    | some e => s!" {e.print}"
    | none => ""
  let alignStr := match gv.align with
    | some a => s!", align {a}"
    | none => ""
  s!"@{gv.name.ToString} = {asStr}{kind} {gv.ty.print}{initStr}{alignStr}"

def TopLevelEntity.print : @TopLevelEntity φ → String
  | .global gv => gv.print
  | .declaration decl => decl.print
  | .definition defn => defn.print

def TopLevel.print : @TopLevel φ → String
  | ⟨.nil⟩ => ""
  | ⟨.cons entity tail⟩ => entity.print ++ "\n" ++ TopLevel.print ⟨tail⟩

end LeanNanoLlvm.AST
