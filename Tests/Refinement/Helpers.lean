import LeanNanoLlvm.Refinement.Tactic
import LeanNanoLlvm.AST.Syntax
import LeanNanoLlvm.AST.Unexpander

/-! Shared helper lemmas (`initCallConfig_*`, entry accessors) for the refinement tests. -/

namespace LeanNanoLlvm.Refinement

open LeanNanoLlvm
open Semantics

def entryTerm (d : AST.Definition) : AST.InstructionId × AST.Terminator :=
  match d.blocks with
  | b :: _ => b.terminator
  | [] => (.void 0, .unreachable)

def entryCode (d : AST.Definition) : AST.Code :=
  match d.blocks with
  | b :: _ => b.code
  | [] => []

theorem initCallConfig_0 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    (ht : defn.prototype.type = .function retTy [] false)
    (ha : defn.args = [])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body)) :
    initCallConfig cfg dl mem ∅ ∅ defn [] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term, registers := ∅ }]
        memory := mem, config := cfg, dataLayout := dl } := by
  simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, applyByValCopies.go,
             ht, ha, hb, hcode, List.length_nil, bne_self_eq_false, Bool.false_or,
             Bool.false_eq_true, ↓reduceIte, ite_self, List.isEmpty_nil, Bool.not_true]

theorem initCallConfig_1 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {pTy : AST.LlvmType} {pId : AST.LocalId}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    {arg : RegisterValue}
    (ht : defn.prototype.type = .function retTy [pTy] false)
    (hpa : defn.prototype.argAttrs = [[]] ∨ defn.prototype.argAttrs = [])
    (ha : defn.args = [pId])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body))
    (hm : arg.matchesType pTy = true) :
    initCallConfig cfg dl mem ∅ ∅ defn [arg] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term,
                     registers := (∅ : AssocMap AST.Identifier RegisterValue).insert (.local_id pId) arg }]
        memory := mem, config := cfg, dataLayout := dl } := by
  rcases hpa with hpa | hpa <;>
  (simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, ht, hpa, ha, hb, hcode, hm,
             List.length_nil, List.length_cons, List.any_nil, List.any_cons, Bool.or_self,
             bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]; rfl)

theorem initCallConfig_2 (cfg : SemanticsConfig) (dl : AST.DataLayout)
    (mem : MemoryState) (defn : AST.Definition) {retTy : AST.LlvmRetType}
    {pTy1 pTy2 : AST.LlvmType} {pId1 pId2 : AST.LocalId}
    {bid : AST.BlockId} {code body : AST.Code} {term : AST.InstructionId × AST.Terminator}
    {arg1 arg2 : RegisterValue}
    (ht : defn.prototype.type = .function retTy [pTy1, pTy2] false)
    (hpa : defn.prototype.argAttrs = [[], []] ∨ defn.prototype.argAttrs = [])
    (ha : defn.args = [pId1, pId2])
    (hb : defn.blocks = [{ id := bid, code := code, terminator := term }])
    (hcode : splitPhis code = ([], body))
    (hm1 : arg1.matchesType pTy1 = true)
    (hm2 : arg2.matchesType pTy2 = true) :
    initCallConfig cfg dl mem ∅ ∅ defn [arg1, arg2] =
      .running {
        frames := [{ defn := defn, curBlock := bid, remainingCode := body,
                     terminator := term,
                     registers := ((∅ : AssocMap AST.Identifier RegisterValue).insert
                       (.local_id pId1) arg1).insert (.local_id pId2) arg2 }]
        memory := mem, config := cfg, dataLayout := dl } := by
  rcases hpa with hpa | hpa <;>
  (simp only [initCallConfig, mkEntryFrameWithMem, mkEntryFrame, bindFrameArgs, bindFrameArgs.go,
             applyByValCopies, ht, hpa, ha, hb, hcode, hm1, hm2,
             List.length_nil, List.length_cons, List.any_nil, List.any_cons, Bool.or_self,
             bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true]; rfl)

end LeanNanoLlvm.Refinement
