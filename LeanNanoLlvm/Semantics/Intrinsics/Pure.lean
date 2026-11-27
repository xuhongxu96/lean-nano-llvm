import LeanNanoLlvm.AST.AST
import LeanNanoLlvm.AST.DataLayout
import LeanNanoLlvm.Semantics.Operations
import LeanNanoLlvm.Util.Text

/-!
# Pure intrinsics

Intrinsics that do not touch memory: integer and bit manipulation, saturating and overflow
arithmetic, vector shuffles and reductions, and floating-point intrinsics (whose NaN, signed-zero
and reduction-order choices draw from the oracle in `llubi`'s order).
-/

namespace LeanNanoLlvm.Semantics

open AST
open RegisterValue (poisonOf)

/-- Pure deterministic (oracle-independent) LLVM intrinsics: saturating shifts, scmp/ucmp,
    smulh/umulh, clmul, pdep/pext, vscale, stepvector, vector reverse/extract/insert/interleave/
    deinterleave/splice, active lane mask, mask.beforefirst, vp.merge, matrix.transpose, and
    experimental vector intrinsics. -/
def evalPureDetIntrinsic? (cfg : SemanticsConfig) (name : String) (retTy : LlvmRetType)
    (_fmf : FastMathFlags) (argVals : List RegisterValue) :
    Option (Except ExecError RegisterValue) :=
  if strHasPrefix name "llvm.sshl.sat" || strHasPrefix name "llvm.ushl.sat" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.sshl.sat"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value amt) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              if amt.toNat ≥ w2 then .ok (.bv w2 .poison)
              else if !isSigned then
                let shifted := x'.toNat <<< amt.toNat
                let res := if shifted ≥ (1 <<< w2) then BitVec.allOnes w2 else BitVec.ofNat w2 shifted
                .ok (.bv w2 (.value res))
              else
                let shifted : Int := x'.toInt * Int.ofNat (1 <<< amt.toNat)
                let hi : Int := Int.ofNat (1 <<< (w2 - 1)) - 1
                let lo : Int := -(Int.ofNat (1 <<< (w2 - 1)))
                let clamped := if shifted > hi then hi else if shifted < lo then lo else shifted
                .ok (.bv w2 (.value (BitVec.ofInt w2 clamped)))
            else .error (.staticError "width mismatch in sshl.sat/ushl.sat")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.scmp" || strHasPrefix name "llvm.ucmp" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.scmp"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i8
        let rw := match resElemTy with | .int w => w | _ => 8
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let cmp : Int :=
                if isSigned then
                  if x'.toInt < y.toInt then -1 else if x'.toInt > y.toInt then 1 else 0
                else
                  if x'.toNat < y.toNat then -1 else if x'.toNat > y.toNat then 1 else 0
              .ok (.bv rw (.value (BitVec.ofInt rw cmp)))
            else .error (.staticError "width mismatch in scmp/ucmp")
          | .bv _ _, _ => .ok (.bv rw .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.smulh" || strHasPrefix name "llvm.umulh" then
    some <| match argVals with
      | [v1, v2] =>
        let isSigned := strHasPrefix name "llvm.smulh"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              if !isSigned then
                .ok (.bv w2 (.value (BitVec.ofNat w2 ((x'.toNat * y.toNat) >>> w2))))
              else
                let prod : Int := x'.toInt * y.toInt
                let q : Int := Int.fdiv prod (Int.ofNat (1 <<< w2))
                .ok (.bv w2 (.value (BitVec.ofInt w2 q)))
            else .error (.staticError "width mismatch in smulh/umulh")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.clmul" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let acc := (List.range w2).foldl (init := 0) fun acc i =>
                if ((y.toNat >>> i) &&& 1) == 1 then acc ^^^ (x'.toNat <<< i) else acc
              .ok (.bv w2 (.value (BitVec.ofNat w2 acc)))
            else .error (.staticError "width mismatch in clmul")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "llvm.clmul expects integer arguments")
      | _ => .error (.staticError "llvm.clmul expects 2 arguments")
  else if strHasPrefix name "llvm.pdep" || strHasPrefix name "llvm.pext" then
    some <| match argVals with
      | [v1, v2] =>
        let isDep := strHasPrefix name "llvm.pdep"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value src), .bv w2 (.value mask) =>
            if h : w1 = w2 then
              let src' : BitVec w2 := h ▸ src
              let (res, _) := (List.range w2).foldl (init := (0, 0)) fun (acc, k) i =>
                if ((mask.toNat >>> i) &&& 1) == 1 then
                  if isDep then
                    let bit := (src'.toNat >>> k) &&& 1
                    (acc ||| (bit <<< i), k + 1)
                  else
                    let bit := (src'.toNat >>> i) &&& 1
                    (acc ||| (bit <<< k), k + 1)
                else (acc, k)
              .ok (.bv w2 (.value (BitVec.ofNat w2 res)))
            else .error (.staticError "width mismatch in pdep/pext")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError s!"{name} expects integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.vscale" then
    some <| match retTy with
      | .ret (.int w) =>
        if cfg.vscale >= (1 <<< w) then .ok (.bv w .poison)
        else .ok (.bv w (.value (BitVec.ofNat w cfg.vscale)))
      | _ => .error (.staticError "llvm.vscale expects integer return type")
  else if strHasPrefix name "llvm.stepvector" then
    some <| match retTy with
      | .ret (.vector n (.int w)) =>
        let elems := (List.range n).map fun i => RegisterValue.bv w (.value (BitVec.ofNat w i))
        .ok (.vector (.int w) elems)
      | _ => .error (.staticError "llvm.stepvector expects integer vector return type")
  else if strHasPrefix name "llvm.vector.reverse" then
    some <| match argVals with
      | [.vector elemTy elems] => .ok (.vector elemTy elems.reverse)
      | _ => .error (.staticError "llvm.vector.reverse expects 1 vector argument")
  else if strHasPrefix name "llvm.vector.extract" then
    some <| match argVals, retTy with
      | [.vector elemTy elems, .bv _ (.value idxBV)], .ret (.vector subLen _) =>
        let idx := idxBV.toNat
        if idx + subLen > elems.length then
          .ok (.vector elemTy (List.replicate subLen (poisonOf elemTy)))
        else
          .ok (.vector elemTy ((elems.drop idx).take subLen))
      | [.vector elemTy _, .bv _ .poison], .ret (.vector subLen _) =>
        .ok (.vector elemTy (List.replicate subLen (poisonOf elemTy)))
      | _, _ => .error (.staticError "llvm.vector.extract expects (vector, int)")
  else if strHasPrefix name "llvm.vector.insert" then
    some <| match argVals with
      | [.vector elemTy dst, .vector _ src, .bv _ (.value idxBV)] =>
        let idx := idxBV.toNat
        if idx + src.length > dst.length then
          .ok (.vector elemTy (List.replicate dst.length (poisonOf elemTy)))
        else
          .ok (.vector elemTy ((dst.take idx) ++ src ++ (dst.drop (idx + src.length))))
      | [.vector elemTy dst, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate dst.length (poisonOf elemTy)))
      | _ => .error (.staticError "llvm.vector.insert expects (vector, vector, int)")
  else if strHasPrefix name "llvm.vector.interleave" then
    some <| match argVals with
      | .vector elemTy first :: rest =>
        let vecs := first :: rest.map (fun | .vector _ es => es | _ => [])
        let n := first.length
        let out := (List.range n).flatMap fun i =>
          vecs.map fun v => v.getD i (poisonOf elemTy)
        .ok (.vector elemTy out)
      | _ => .error (.staticError s!"{name} expects vector arguments")
  else if strHasPrefix name "llvm.vector.deinterleave" then
    some <| match argVals, retTy with
      | [.vector elemTy elems], .ret (.struct packed fieldTys) =>
        let k := fieldTys.length
        if k == 0 then .error (.staticError s!"{name}: empty struct return")
        else
          let n := elems.length / k
          let fields := (List.range k).map fun j =>
            RegisterValue.vector elemTy ((List.range n).map fun i => elems.getD (i * k + j) (poisonOf elemTy))
          .ok (.struct packed fieldTys fields)
      | _, _ => .error (.staticError s!"{name} expects 1 vector argument and struct return")
  else if strHasPrefix name "llvm.vector.splice.left" || strHasPrefix name "llvm.vector.splice.right" then
    some <| match argVals with
      | [.vector elemTy v1, .vector _ v2, .bv _ (.value idxBV)] =>
        let len := v1.length
        let idx := idxBV.toNat
        if idx > len then
          .ok (.vector elemTy (List.replicate len (poisonOf elemTy)))
        else if strHasPrefix name "llvm.vector.splice.left" then
          .ok (.vector elemTy ((v1.drop idx) ++ (v2.take idx)))
        else
          let off := len - idx
          .ok (.vector elemTy ((v1.drop off) ++ (v2.take off)))
      | [.vector elemTy v1, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate v1.length (poisonOf elemTy)))
      | _ => .error (.staticError s!"{name} expects (vector, vector, int)")
  else if strHasPrefix name "llvm.get.active.lane.mask" then
    some <| match argVals, retTy with
      | [.bv _ (.value baseBV), .bv _ (.value nBV)], .ret (.vector len .i1) =>
        let base := baseBV.toNat
        let n := nBV.toNat
        let elems := (List.range len).map fun i =>
          let active := base < n && i < n - base
          RegisterValue.bv 1 (.value (BitVec.ofBool active))
        .ok (.vector .i1 elems)
      | [.bv _ _, .bv _ _], .ret (.vector len .i1) =>
        .ok (.vector .i1 (List.replicate len (.bv 1 .poison)))
      | _, _ => .error (.staticError "llvm.get.active.lane.mask expects 2 integers and <N x i1> return")
  else if strHasPrefix name "llvm.mask.beforefirst" then
    some <| match argVals with
      | [.vector .i1 elems] =>
        if elems.any RegisterValue.isScalarPoison then
          .ok (.vector .i1 (List.replicate elems.length (.bv 1 .poison)))
        else
          let rec go (seenTrue : Bool) : List RegisterValue → List RegisterValue
            | [] => []
            | e :: es =>
              if seenTrue then .bv 1 (.value 0#1) :: go true es
              else match e with
                | .bv 1 (.value b) =>
                  if b == 1#1 then .bv 1 (.value 0#1) :: go true es
                  else .bv 1 (.value 1#1) :: go false es
                | _ => .bv 1 .poison :: go false es
          .ok (.vector .i1 (go false elems))
      | _ => .error (.staticError "llvm.mask.beforefirst expects <N x i1>")
  else if strHasPrefix name "llvm.vp.merge" then
    some <| match argVals with
      | [.vector _ mask, .vector elemTy onTrue, .vector _ onFalse, .bv _ (.value evlBV)] =>
        let len := onTrue.length
        let evl := evlBV.toNat
        if evl > len then
          .ok (.vector elemTy (List.replicate len (poisonOf elemTy)))
        else
          let out := (List.range len).map fun i =>
            if i ≥ evl then onFalse.getD i (poisonOf elemTy)
            else match mask.getD i (.bv 1 .poison) with
              | .bv 1 (.value b) =>
                if b == 1#1 then onTrue.getD i (poisonOf elemTy)
                else onFalse.getD i (poisonOf elemTy)
              | _ => poisonOf elemTy
          .ok (.vector elemTy out)
      | [.vector _ _, .vector elemTy onTrue, .vector _ _, .bv _ .poison] =>
        .ok (.vector elemTy (List.replicate onTrue.length (poisonOf elemTy)))
      | _ => .error (.staticError "llvm.vp.merge expects (mask, onTrue, onFalse, evl)")
  else if strHasPrefix name "llvm.matrix.transpose" then
    some <| match argVals with
      | [.vector elemTy elems, .bv _ (.value rBV), .bv _ (.value cBV)] =>
        let rows := rBV.toNat
        let cols := cBV.toNat
        let out := (List.range rows).flatMap fun r =>
          (List.range cols).map fun c =>
            elems.getD (c * rows + r) (poisonOf elemTy)
        .ok (.vector elemTy out)
      | _ => .error (.staticError "llvm.matrix.transpose expects (vector, rows, cols)")
  else if strHasPrefix name "llvm.experimental.cttz.elts" then
    some <| match argVals, retTy with
      | [.vector _ elems, .bv 1 (.value zpBV)], .ret (.int rw) =>
        if elems.any RegisterValue.isScalarPoison then .ok (.bv rw .poison)
        else
          let isZeroPoison := zpBV == 1#1
          let rec goCttz (idx : Nat) : List RegisterValue → RegisterValue
            | [] => if isZeroPoison then .bv rw .poison else .bv rw (.value (BitVec.ofNat rw elems.length))
            | e :: es =>
              match e with
              | .bv _ (.value b) => if b.toNat != 0 then .bv rw (.value (BitVec.ofNat rw idx)) else goCttz (idx + 1) es
              | _ => .bv rw .poison
          .ok (goCttz 0 elems)
      | [_, _], .ret (.int rw) => .ok (.bv rw .poison)
      | _, _ => .error (.staticError "llvm.experimental.cttz.elts expects (vector, i1)")
  else if strHasPrefix name "llvm.experimental.get.vector.length" then
    some <| match argVals, retTy with
      | [.bv _ (.value cntBV), .bv _ (.value vfBV), .bv 1 (.value scBV)], .ret (.int rw) =>
        let mult := if scBV == 1#1 then cfg.vscale else 1
        let maxLanes := vfBV.toNat * mult
        .ok (.bv rw (.value (BitVec.ofNat rw (min cntBV.toNat maxLanes))))
      | [_, _, _], .ret (.int rw) => .ok (.bv rw .poison)
      | _, _ => .error (.staticError "llvm.experimental.get.vector.length expects (cnt, vf, scalable)")
  else if strHasPrefix name "llvm.experimental.vector.compress" then
    some <| match argVals with
      | [.vector elemTy vec, .vector _ mask, .vector _ passthru] =>
        let hasPoisonMask := mask.any fun | .bv 1 (.value _) => false | _ => true
        if hasPoisonMask then
          .ok (.vector elemTy (List.replicate vec.length (poisonOf elemTy)))
        else
          let active := (List.range vec.length).filterMap fun i =>
            match mask.getD i (.bv 1 (.value 0#1)) with
            | .bv 1 (.value b) => if b == 1#1 then some (vec.getD i (poisonOf elemTy)) else none
            | _ => none
          let out := active ++ (passthru.drop active.length)
          .ok (.vector elemTy (out.take vec.length))
      | _ => .error (.staticError "llvm.experimental.vector.compress expects (vec, mask, passthru)")
  else if strHasPrefix name "llvm.experimental.vector.extract.last.active" then
    some <| match argVals with
      | [.vector elemTy vec, .vector _ mask, passthru] =>
        let rec findLast : List (RegisterValue × RegisterValue) → RegisterValue
          | [] => passthru
          | (v, m) :: rest =>
            match m with
            | .bv 1 (.value b) => if b == 1#1 then v else findLast rest
            | _ => poisonOf elemTy
        .ok (findLast (vec.zip mask).reverse)
      | _ => .error (.staticError "llvm.experimental.vector.extract.last.active expects (vec, mask, passthru)")
  else if strHasPrefix name "llvm.experimental.vector.match" then
    some <| match argVals with
      | [.vector _ vec, .vector _ setElems, .vector _ mask] =>
        let hasPoisonSet := setElems.any (·.containsPoison)
        let out := (vec.zip mask).map fun (x, m) =>
          match m with
          | .bv 1 (.value b) =>
            if b == 0#1 then RegisterValue.bv 1 (.value 0#1)
            else if x.containsPoison || hasPoisonSet then RegisterValue.bv 1 .poison
            else if setElems.any (fun s => !s.containsPoison && s == x) then RegisterValue.bv 1 (.value 1#1)
            else RegisterValue.bv 1 (.value 0#1)
          | _ => RegisterValue.bv 1 .poison
        .ok (.vector .i1 out)
      | [.vector _ vec, .vector _ setElems] =>
        let hasPoisonSet := setElems.any (·.containsPoison)
        let out := vec.map fun x =>
          if x.containsPoison then RegisterValue.bv 1 .poison
          else if setElems.any (fun s => !s.containsPoison && s == x) then RegisterValue.bv 1 (.value 1#1)
          else if hasPoisonSet then RegisterValue.bv 1 .poison
          else RegisterValue.bv 1 (.value 0#1)
        .ok (.vector .i1 out)
      | _ => .error (.staticError "llvm.experimental.vector.match expects (vec, set[, mask])")
  else if strHasPrefix name "llvm.vector.reduce.add" || strHasPrefix name "llvm.vector.reduce.mul" ||
          strHasPrefix name "llvm.vector.reduce.and" || strHasPrefix name "llvm.vector.reduce.or" ||
          strHasPrefix name "llvm.vector.reduce.xor" || strHasPrefix name "llvm.vector.reduce.smax" ||
          strHasPrefix name "llvm.vector.reduce.smin" || strHasPrefix name "llvm.vector.reduce.umax" ||
          strHasPrefix name "llvm.vector.reduce.umin" then
    some <| match argVals with
      | [.vector _ (first :: rest)] =>
        let combine {w : Nat} (a b : BitVec w) : BitVec w :=
          if strHasPrefix name "llvm.vector.reduce.add" then a + b
          else if strHasPrefix name "llvm.vector.reduce.mul" then a * b
          else if strHasPrefix name "llvm.vector.reduce.and" then a &&& b
          else if strHasPrefix name "llvm.vector.reduce.or" then a ||| b
          else if strHasPrefix name "llvm.vector.reduce.xor" then a ^^^ b
          else if strHasPrefix name "llvm.vector.reduce.smax" then if a.toInt ≥ b.toInt then a else b
          else if strHasPrefix name "llvm.vector.reduce.smin" then if a.toInt ≤ b.toInt then a else b
          else if strHasPrefix name "llvm.vector.reduce.umax" then if a.toNat ≥ b.toNat then a else b
          else if a.toNat ≤ b.toNat then a else b
        let rec goIntRed (acc : RegisterValue) : List RegisterValue → Except ExecError RegisterValue
          | [] => .ok acc
          | e :: es =>
            match acc, e with
            | .bv w1 (.value a), .bv w2 (.value b) =>
              if h : w1 = w2 then goIntRed (.bv w2 (.value (combine (h ▸ a) b))) es
              else .error (.staticError s!"width mismatch in {name}")
            | .bv w _, .bv _ _ => goIntRed (.bv w .poison) es
            | _, _ => .error (.staticError s!"expected integer elements in {name}")
        goIntRed first rest
      | _ => .error (.staticError s!"{name} expects a non-empty integer vector")
  else
    none

/-- The float payloads of `es` if all are floats of type `ft`. -/
def floatsOf (ft : FloatType) : List RegisterValue → Option (List (PoisonOr (IEEEFloat ft.format)))
  | [] => some []
  | .float ft' v :: rest =>
    if h : ft' = ft then (floatsOf ft rest).map ((h ▸ v) :: ·) else none
  | _ :: _ => none

/-- Validate min/max reduction inputs (poison, `nnan`/`ninf`) and draw their input denormal
choices, stopping at the first invalid input. -/
def prepMinMaxInputs {fmt : FloatFormat} (cfg : SemanticsConfig) (fmf : FastMathFlags) :
    List (PoisonOr (IEEEFloat fmt)) → OracleState → Option (List (IEEEFloat fmt)) × OracleState
  | [], o => (some [], o)
  | .poison :: _, o => (none, o)
  | .value x :: xs, o =>
    match fmfIn fmf x o with
    | (.poison, o1) => (none, o1)
    | (.value x', o1) =>
      match denormIn cfg.denormalMode.input x' o1 with
      | (fx, o2) =>
        match prepMinMaxInputs cfg fmf xs o2 with
        | (some rest, o3) => (some (fx :: rest), o3)
        | (none, o3) => (none, o3)

/-- `llvm.vector.reduce.fmaximum/fminimum/...num`: validate, flush and combine element by element. -/
def foldMinMaxO {fmt : FloatFormat} (cfg : SemanticsConfig) (k : FPMinMaxKind) (fmf : FastMathFlags)
    (nsz : Bool) : List (PoisonOr (IEEEFloat fmt)) → Option (IEEEFloat fmt) → OracleState →
    Option (IEEEFloat fmt) × OracleState
  | [], acc, o => (acc, o)
  | .poison :: _, _, o => (none, o)
  | .value x :: xs, acc, o =>
    match fmfIn fmf x o with
    | (.poison, o1) => (none, o1)
    | (.value x', o1) =>
      match denormIn cfg.denormalMode.input x' o1 with
      | (fx, o2) =>
        match acc with
        | none => foldMinMaxO cfg k fmf nsz xs (some fx) o2
        | some a =>
          match applyFPMinMaxO k nsz a fx o2 with
          | (r, o3) => foldMinMaxO cfg k fmf nsz xs (some r) o3

/-- `llvm.vector.reduce.fmax/fmin` reduction: with an sNaN input the pairing order is chosen
nondeterministically (two draws per combination step), as `llubi`'s work-list reduction does. -/
def reducePairwiseO {fmt : FloatFormat} (k : FPMinMaxKind) (nsz hasSNaN : Bool) :
    List (IEEEFloat fmt) → OracleState → IEEEFloat fmt × OracleState
  | ws, o =>
    let rec go (fuel : Nat) (ws : List (IEEEFloat fmt)) (o : OracleState) : IEEEFloat fmt × OracleState :=
      match fuel, ws with
      | 0, _ | _, [] => (ws.headD (IEEEFloat.zero fmt), o)
      | _, [w] => (w, o)
      | fuel' + 1, _ =>
        let n := ws.length
        let (li, ri, o1) : Nat × Nat × OracleState :=
          if hasSNaN then
            match o.nextNat with
            | (a, oa) =>
              match oa.nextNat with
              | (b, ob) =>
                let l := a % n
                let r := b % (n - 1)
                (l, if r ≥ l then r + 1 else r, ob)
          else (0, 1, o)
        match applyFPMinMaxO k nsz (ws.getD li (IEEEFloat.zero fmt)) (ws.getD ri (IEEEFloat.zero fmt)) o1 with
        | (res, o2) =>
          let hi := max li ri
          let lo := min li ri
          let ws' := ((ws.eraseIdx hi).eraseIdx lo) ++ [res]
          go fuel' ws' o2
    go ws.length ws o

/-- Pure non-memory LLVM intrinsics (integer, bit-manipulation, saturating, overflow, FP, assume). -/
def evalPureIntrinsicExec? (cfg : SemanticsConfig) (name : String) (retTy : LlvmRetType)
    (fmf : FastMathFlags) (argVals : List RegisterValue) (o : OracleState) :
    Option (Except ExecError (RegisterValue × OracleState)) :=
  if name == "llvm.assume" then
    some <| match argVals with
      | [.bv 1 (.value b)] =>
        if b == 0 then .error (.immediateUB "Assume on false or poison condition.") else .ok (.void, o)
      | [.bv 1 .poison] => .error (.immediateUB "The value poison violates noundef attribute.")
      | _ => .error (.staticError "llvm.assume expects i1 argument")
  else if name == "llvm.donothing" || name == "llvm.experimental.noalias.scope.decl" ||
          name == "llvm.inlineasm.noop" then
    some (.ok (.void, o))
  else if strHasPrefix name "llvm.ssa.copy" || strHasPrefix name "llvm.expect" then
    some <| match argVals with
      | v :: _ => .ok (v, o)
      | [] => .error (.staticError s!"{name} requires at least 1 argument")
  else if strHasPrefix name "llvm.abs" then
    some <| match argVals with
      | [v, .bv 1 (.value isIntMinPoison)] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            if isIntMinPoison != 0 && x == BitVec.intMin w then .ok (.bv w .poison)
            else .ok (.bv w (.value (if x.msb then -x else x)))
          | other => .error (.staticError s!"Expected int in llvm.abs, got {other}")).map (·, o)
      | _ => .error (.staticError "llvm.abs expects (int, i1)")
  else if strHasPrefix name "llvm.smax" || strHasPrefix name "llvm.smin" ||
          strHasPrefix name "llvm.umax" || strHasPrefix name "llvm.umin" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let pickX :=
                if strHasPrefix name "llvm.smax" then BitVec.sle y x'
                else if strHasPrefix name "llvm.smin" then BitVec.sle x' y
                else if strHasPrefix name "llvm.umax" then y ≤ x'
                else x' ≤ y
              .ok (.bv w2 (.value (if pickX then x' else y)))
            else .error (.staticError "width mismatch in min/max intrinsic")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "Expected int in min/max intrinsic")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.ctlz" || strHasPrefix name "llvm.cttz" then
    some <| match argVals with
      | [v, .bv 1 (.value isZeroPoison)] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        let isLeading := strHasPrefix name "llvm.ctlz"
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            if isZeroPoison != 0 && x == 0 then .ok (.bv w .poison)
            else .ok (.bv w (.value (if isLeading then bvCtlz x else bvCttz x)))
          | other => .error (.staticError s!"Expected int in ctlz/cttz, got {other}")).map (·, o)
      | _ => .error (.staticError s!"{name} expects (int, i1)")
  else if strHasPrefix name "llvm.ctpop" || strHasPrefix name "llvm.bitreverse" || strHasPrefix name "llvm.bswap" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftUnaryPure resElemTy v fun
          | .bv w .poison => .ok (.bv w .poison)
          | .bv w (.value x) =>
            let res :=
              if strHasPrefix name "llvm.ctpop" then bvCtpop x
              else if strHasPrefix name "llvm.bitreverse" then bvBitReverse x
              else bvBSwap x
            .ok (.bv w (.value res))
          | other => .error (.staticError s!"Expected int in {name}, got {other}")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else if strHasPrefix name "llvm.fshl" || strHasPrefix name "llvm.fshr" then
    some <| match argVals with
      | [v1, v2, v3] =>
        let isLeft := strHasPrefix name "llvm.fshl"
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        let doScalar (a b c : RegisterValue) : Except ExecError RegisterValue :=
          match a, b, c with
          | .bv w1 (.value x), .bv w2 (.value y), .bv w3 (.value amt) =>
            if h1 : w1 = w3 then
              if h2 : w2 = w3 then
                let r := if isLeft then bvFshl (h1 ▸ x) (h2 ▸ y) amt else bvFshr (h1 ▸ x) (h2 ▸ y) amt
                .ok (.bv w3 (.value r))
              else .error (.staticError "width mismatch in fshl/fshr")
            else .error (.staticError "width mismatch in fshl/fshr")
          | .bv w _, _, _ => .ok (.bv w .poison)
          | _, _, _ => .error (.staticError s!"{name} expects 3 integer arguments")
        match v1, v2, v3 with
        | .vector _ xs, .vector _ ys, .vector _ zs =>
          let rec go : List RegisterValue → List RegisterValue → List RegisterValue → Except ExecError (List RegisterValue)
            | [], [], [] => .ok []
            | a :: as, b :: bs, c :: cs => do
              let r ← doScalar a b c
              let rs ← go as bs cs
              .ok (r :: rs)
            | _, _, _ => .error (.staticError "mismatched vector lengths in fshl/fshr")
          (go xs ys zs).map fun rs => (.vector resElemTy rs, o)
        | _, _, _ => (doScalar v1 v2 v3).map (·, o)
      | _ => .error (.staticError s!"{name} expects 3 integer arguments")
  else if strHasPrefix name "llvm.sadd.sat" || strHasPrefix name "llvm.uadd.sat" ||
          strHasPrefix name "llvm.ssub.sat" || strHasPrefix name "llvm.usub.sat" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .i32
        (liftBinaryPure resElemTy v1 v2 fun a b =>
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let res :=
                if strHasPrefix name "llvm.sadd.sat" then bvSAddSat x' y
                else if strHasPrefix name "llvm.uadd.sat" then bvUAddSat x' y
                else if strHasPrefix name "llvm.ssub.sat" then bvSSubSat x' y
                else bvUSubSat x' y
              .ok (.bv w2 (.value res))
            else .error (.staticError "width mismatch in saturating intrinsic")
          | .bv w _, _ => .ok (.bv w .poison)
          | _, _ => .error (.staticError "Expected int in saturating intrinsic")).map (·, o)
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.sadd.with.overflow" || strHasPrefix name "llvm.uadd.with.overflow" ||
          strHasPrefix name "llvm.ssub.with.overflow" || strHasPrefix name "llvm.usub.with.overflow" ||
          strHasPrefix name "llvm.smul.with.overflow" || strHasPrefix name "llvm.umul.with.overflow" then
    some <| match argVals with
      | [v1, v2] =>
        let doScalar (a b : RegisterValue) : Except ExecError (RegisterValue × RegisterValue) :=
          match a, b with
          | .bv w1 (.value x), .bv w2 (.value y) =>
            if h : w1 = w2 then
              let x' : BitVec w2 := h ▸ x
              let (res, ov) :=
                if strHasPrefix name "llvm.sadd" then (x' + y, BitVec.saddOverflow x' y)
                else if strHasPrefix name "llvm.uadd" then (x' + y, BitVec.uaddOverflow x' y)
                else if strHasPrefix name "llvm.ssub" then (x' - y, BitVec.ssubOverflow x' y)
                else if strHasPrefix name "llvm.usub" then (x' - y, BitVec.usubOverflow x' y)
                else if strHasPrefix name "llvm.smul" then (x' * y, BitVec.smulOverflow x' y)
                else (x' * y, BitVec.umulOverflow x' y)
              .ok (.bv w2 (.value res), .bv 1 (.value (BitVec.ofBool ov)))
            else .error (.staticError "width mismatch in with.overflow intrinsic")
          | .bv w _, _ => .ok (.bv w .poison, .bv 1 .poison)
          | _, _ => .error (.staticError s!"{name} expects 2 integer arguments")
        match v1, v2 with
        | .vector elemTy xs, .vector _ ys =>
          let rec goOv : List RegisterValue → List RegisterValue → Except ExecError (List RegisterValue × List RegisterValue)
            | [], [] => .ok ([], [])
            | a :: as, b :: bs => do
              let (r, ov) ← doScalar a b
              let (rs, ovs) ← goOv as bs
              .ok (r :: rs, ov :: ovs)
            | _, _ => .error (.staticError "mismatched vector lengths in with.overflow intrinsic")
          (goOv xs ys).map fun (rs, ovs) =>
            let n := xs.length
            (.struct false [.vector n elemTy, .vector n .i1] [.vector elemTy rs, .vector .i1 ovs], o)
        | .bv w _, _ =>
          (doScalar v1 v2).map fun (r, ov) => (.struct false [.int w, .int 1] [r, ov], o)
        | _, _ => .error (.staticError s!"{name} expects 2 integer arguments")
      | _ => .error (.staticError s!"{name} expects 2 integer arguments")
  else if strHasPrefix name "llvm.fabs" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (e : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match e with
          | .float ft .poison => .ok (.float ft .poison, o0)
          | .float ft (.value flt) =>
            match fmfIn fmf flt o0 with
            | (.poison, o1) => .ok (.float ft .poison, o1)
            | (.value f', o1) => .ok (.float ft (handleFMF fmf false false f'.abs), o1)
          | other => .error (.staticError s!"Expected float in llvm.fabs, got {other}")
        match v with
        | .vector _ elems =>
          (mapListOracle goElem elems o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _ => goElem v o
      | _ => .error (.staticError "llvm.fabs expects 1 argument")
  else if strHasPrefix name "llvm.copysign" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match a, b with
          | .float ft1 (.value m), .float ft2 (.value sg) =>
            if h : ft1 = ft2 then
              match fmfIn fmf (h ▸ m) o0 with
              | (vm, o1) =>
                match fmfIn fmf sg o1 with
                | (vs, o2) =>
                  match vm, vs with
                  | .value m', .value s' => .ok (.float ft2 (handleFMF fmf false false (m'.copySign s')), o2)
                  | _, _ => .ok (.float ft2 .poison, o2)
            else .error (.staticError "Mismatched float types in llvm.copysign")
          | .float ft _, _ => .ok (.float ft .poison, o0)
          | _, _ => .error (.staticError "Expected floats in llvm.copysign")
        match v1, v2 with
        | .vector _ es1, .vector _ es2 =>
          (mapList2Oracle goElem es1 es2 o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _, _ => goElem v1 v2 o
      | _ => .error (.staticError "llvm.copysign expects 2 arguments")
  else if strHasPrefix name "llvm.fma" || strHasPrefix name "llvm.fmuladd" then
    some <| match argVals with
      | [v1, v2, v3] =>
        let useFma := strHasPrefix name "llvm.fma" || cfg.fuseFMulAdd
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let doScalar (ea eb ec : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match ea, eb, ec with
          | .float ft1 (.value a), .float ft2 (.value b), .float ft3 (.value c) =>
            if h1 : ft1 = ft3 then
              if h2 : ft2 = ft3 then
                match fmfIn fmf (h1 ▸ a) o0 with
                | (va, o1) =>
                  match fmfIn fmf (h2 ▸ b) o1 with
                  | (vb, o2) =>
                    match fmfIn fmf c o2 with
                    | (vc, o3) =>
                      match va, vb, vc with
                      | .value a', .value b', .value c' =>
                        match denormIn cfg.denormalMode.input a' o3 with
                        | (fa, o4) =>
                          match denormIn cfg.denormalMode.input b' o4 with
                          | (fb, o5) =>
                            match denormIn cfg.denormalMode.input c' o5 with
                            | (fc, o6) =>
                              let raw :=
                                if useFma then IEEEFloat.fma cfg.roundingMode fa fb fc
                                else IEEEFloat.add cfg.roundingMode (IEEEFloat.mul cfg.roundingMode fa fb) fc
                              let flushed := handleDenormal cfg.denormalMode.output false false raw
                              match handleFMF fmf false false flushed with
                              | .poison => .ok (.float ft3 .poison, o6)
                              | .value r =>
                                match nanPropagate cfg.nanMode r [fa, fb, fc] o6 with
                                | (fin, o7) => .ok (.float ft3 (.value fin), o7)
                      | _, _, _ => .ok (.float ft3 .poison, o3)
              else .error (.staticError "Mismatched float types in llvm.fma")
            else .error (.staticError "Mismatched float types in llvm.fma")
          | .float ft _, _, _ => .ok (.float ft .poison, o0)
          | _, _, _ => .error (.staticError s!"{name} expects 3 float arguments")
        match v1, v2, v3 with
        | .vector _ xs, .vector _ ys, .vector _ zs =>
          let rec goFma : List RegisterValue → List RegisterValue → List RegisterValue → OracleState →
              Except ExecError (List RegisterValue × OracleState)
            | [], [], [], o0 => .ok ([], o0)
            | a :: as, b :: bs, c :: cs, o0 => do
              let (r, o1) ← doScalar a b c o0
              let (rs, o2) ← goFma as bs cs o1
              .ok (r :: rs, o2)
            | _, _, _, _ => .error (.staticError "Mismatched vector lengths in llvm.fma")
          (goFma xs ys zs o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _, _, _ => doScalar v1 v2 v3 o
      | _ => .error (.staticError s!"{name} expects 3 float arguments")
  else if strHasPrefix name "llvm.minimum" || strHasPrefix name "llvm.maximum" ||
          strHasPrefix name "llvm.minnum" || strHasPrefix name "llvm.maxnum" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let kind : FPMinMaxKind :=
          if strHasPrefix name "llvm.minimumnum" then .minimumnum
          else if strHasPrefix name "llvm.maximumnum" then .maximumnum
          else if strHasPrefix name "llvm.minnum" then .minnum
          else if strHasPrefix name "llvm.maxnum" then .maxnum
          else if strHasPrefix name "llvm.minimum" then .minimum
          else .maximum
        let inFmf : FastMathFlags := { fmf with nsz := false }
        let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match a, b with
          | .float ft1 (.value x), .float ft2 (.value y) =>
            if h : ft1 = ft2 then
              match fmfIn inFmf (h ▸ x) o0 with
              | (vx, o1) =>
                match fmfIn inFmf y o1 with
                | (vy, o2) =>
                  match vx, vy with
                  | .value x', .value y' =>
                    match denormIn cfg.denormalMode.input x' o2 with
                    | (fx, o3) =>
                      match denormIn cfg.denormalMode.input y' o3 with
                      | (fy, o4) =>
                        match applyFPMinMaxO kind fmf.nsz fx fy o4 with
                        | (raw, o5) =>
                          let flushed := handleDenormal cfg.denormalMode.output false false raw
                          match handleFMF inFmf false false flushed with
                          | .poison => .ok (.float ft2 .poison, o5)
                          | .value r =>
                            match nanPropagate cfg.nanMode r [fx, fy] o5 with
                            | (fin, o6) => .ok (.float ft2 (.value fin), o6)
                  | _, _ => .ok (.float ft2 .poison, o2)
            else .error (.staticError "Mismatched float types in FP min/max")
          | .float ft _, _ => .ok (.float ft .poison, o0)
          | _, _ => .error (.staticError "Expected floats in FP min/max")
        match v1, v2 with
        | .vector _ es1, .vector _ es2 =>
          if es1.length != es2.length then .error (.staticError "Vector length mismatch in FP min/max")
          else (mapList2Oracle goElem es1 es2 o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _, _ => goElem v1 v2 o
      | _ => .error (.staticError s!"{name} expects 2 arguments")
  else if strHasPrefix name "llvm.is.fpclass" then
    some <| match argVals with
      | [v, .bv _ (.value mask)] =>
        (liftUnaryPure .i1 v fun
          | .float _ .poison => .ok (.bv 1 .poison)
          | .float _ (.value flt) =>
            .ok (.bv 1 (.value (BitVec.ofBool ((flt.fpClassBit &&& mask.toNat) != 0))))
          | other => .error (.staticError s!"Expected float in llvm.is.fpclass, got {other}")).map (·, o)
      | _ => .error (.staticError "llvm.is.fpclass expects (float, i32)")
  else if strHasPrefix name "llvm.fptosi.sat" || strHasPrefix name "llvm.fptoui.sat" then
    some <| match argVals with
      | [v] =>
        let isSigned := strHasPrefix name "llvm.fptosi.sat"
        match retTy with
        | .ret rTy =>
          match rTy.scalarType with
          | .int dstW =>
            (liftUnaryPure (.int dstW) v fun
              | .float _ .poison => .ok (.bv dstW .poison)
              | .float _ (.value flt) =>
                let bv := if isSigned then flt.toSignedBitVecSat dstW else flt.toUnsignedBitVecSat dstW
                .ok (.bv dstW (.value bv))
              | other => .error (.staticError s!"Expected float in fpto[su]i.sat, got {other}")).map (·, o)
          | _ => .error (.staticError "Expected integer return type for fpto[su]i.sat")
        | .void => .error (.staticError "fpto[su]i.sat cannot return void")
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else if strHasPrefix name "llvm.ceil" || strHasPrefix name "llvm.floor" ||
          strHasPrefix name "llvm.trunc" || strHasPrefix name "llvm.roundeven" ||
          strHasPrefix name "llvm.round" || strHasPrefix name "llvm.rint" ||
          strHasPrefix name "llvm.nearbyint" || strHasPrefix name "llvm.canonicalize" ||
          strHasPrefix name "llvm.sqrt" then
    some <| match argVals with
      | [v] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let applyUnaryOp {fmt : FloatFormat} (x : IEEEFloat fmt) : IEEEFloat fmt :=
          if strHasPrefix name "llvm.ceil" then x.ceil
          else if strHasPrefix name "llvm.floor" then x.floor
          else if strHasPrefix name "llvm.trunc" then x.trunc
          else if strHasPrefix name "llvm.roundeven" then x.roundeven
          else if strHasPrefix name "llvm.round" then x.round
          else if strHasPrefix name "llvm.rint" || strHasPrefix name "llvm.nearbyint" then
            x.roundToIntegral cfg.roundingMode
          else if strHasPrefix name "llvm.canonicalize" then x.canonicalize
          else x.sqrt cfg.roundingMode
        let goElem (e : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match e with
          | .float ft .poison => .ok (.float ft .poison, o0)
          | .float ft (.value flt) =>
            match fmfIn fmf flt o0 with
            | (.poison, o1) => .ok (.float ft .poison, o1)
            | (.value f', o1) =>
              match handleFMF fmf false false (applyUnaryOp f') with
              | .poison => .ok (.float ft .poison, o1)
              | .value r =>
                match nanPropagate cfg.nanMode r [f'] o1 with
                | (fin, o2) => .ok (.float ft (.value fin), o2)
          | other => .error (.staticError s!"Expected float in {name}, got {other}")
        match v with
        | .vector _ elems =>
          (mapListOracle goElem elems o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _ => goElem v o
      | _ => .error (.staticError s!"{name} expects 1 argument")
  else if strHasPrefix name "llvm.ldexp" then
    some <| match argVals with
      | [v1, v2] =>
        let resElemTy := match retTy with | .ret t => t.scalarType | .void => .f32
        let goElem (a b : RegisterValue) (o0 : OracleState) : Except ExecError (RegisterValue × OracleState) :=
          match a, b with
          | .float ft (.value flt), .bv _ (.value expBv) =>
            match fmfIn fmf flt o0 with
            | (.poison, o1) => .ok (.float ft .poison, o1)
            | (.value f', o1) =>
              match handleFMF fmf false false (f'.ldexp cfg.roundingMode expBv.toInt) with
              | .poison => .ok (.float ft .poison, o1)
              | .value r =>
                match nanPropagate cfg.nanMode r [f'] o1 with
                | (fin, o2) => .ok (.float ft (.value fin), o2)
          | .float ft _, .bv _ _ => .ok (.float ft .poison, o0)
          | _, _ => .error (.staticError "Expected (float, int) in llvm.ldexp")
        match v1, v2 with
        | .vector _ es1, .vector _ es2 =>
          if es1.length != es2.length then .error (.staticError "Vector length mismatch in llvm.ldexp")
          else (mapList2Oracle goElem es1 es2 o).map fun (rs, o') => (.vector resElemTy rs, o')
        | _, _ => goElem v1 v2 o
      | _ => .error (.staticError "llvm.ldexp expects 2 arguments")
  else if strHasPrefix name "llvm.vector.reduce.fadd" || strHasPrefix name "llvm.vector.reduce.fmul" then
    some <| match argVals with
      | [startV, .vector _ elems] =>
        let op : FloatBinaryOp := if strHasPrefix name "llvm.vector.reduce.fadd" then .fadd fmf else .fmul fmf
        -- sequential reduction; stops (without further draws) as soon as the result is poison
        let rec goFold (acc : RegisterValue) (es : List RegisterValue) (o0 : OracleState) :
            Except ExecError (RegisterValue × OracleState) :=
          match es with
          | [] => .ok (acc, o0)
          | e :: rest =>
            match acc, e with
            | .float _ .poison, _ => .ok (acc, o0)
            | .float ft1 fa, .float ft2 fb =>
              if h : ft1 = ft2 then
                match evalFloatBinaryOp cfg op (h ▸ fa) fb o0 with
                | (.poison, o1) => .ok (.float ft2 .poison, o1)
                | (r, o1) => goFold (.float ft2 r) rest o1
              else .error (.staticError s!"Mismatched float types in {name}")
            | _, _ => .error (.staticError s!"Expected float elements in {name}")
        goFold startV elems o
      | _ => .error (.staticError s!"{name} expects (float, vector) arguments")
  else if strHasPrefix name "llvm.vector.reduce.fmaximumnum" || strHasPrefix name "llvm.vector.reduce.fminimumnum" ||
          strHasPrefix name "llvm.vector.reduce.fmaximum" || strHasPrefix name "llvm.vector.reduce.fminimum" ||
          strHasPrefix name "llvm.vector.reduce.fmax" || strHasPrefix name "llvm.vector.reduce.fmin" then
    some <| match argVals with
      | [.vector _ elems@(.float ft _ :: _)] =>
        let kind : FPMinMaxKind :=
          if strHasPrefix name "llvm.vector.reduce.fminimumnum" then .minimumnum
          else if strHasPrefix name "llvm.vector.reduce.fmaximumnum" then .maximumnum
          else if strHasPrefix name "llvm.vector.reduce.fminimum" then .minimum
          else if strHasPrefix name "llvm.vector.reduce.fmaximum" then .maximum
          else if strHasPrefix name "llvm.vector.reduce.fmin" then .minnum
          else .maxnum
        let inFmf : FastMathFlags := { fmf with nsz := false }
        match floatsOf ft elems with
        | none => .error (.staticError s!"Expected float elements of one type in {name}")
        | some xs =>
          let vals := xs.filterMap fun | .value x => some x | .poison => none
          let combined : Option (IEEEFloat ft.format × List (IEEEFloat ft.format)) × OracleState :=
            if kind == .maxnum || kind == .minnum then
              -- all inputs are validated first, then reduced in a (possibly random) order
              match prepMinMaxInputs cfg inFmf xs o with
              | (none, o1) => (none, o1)
              | (some ins, o1) =>
                match reducePairwiseO kind fmf.nsz (ins.any IEEEFloat.isSNaN) ins o1 with
                | (r, o2) => (some (r, ins), o2)
            else
              -- inputs are validated and combined one at a time
              match foldMinMaxO cfg kind inFmf fmf.nsz xs none o with
              | (some r, o1) => (some (r, vals), o1)
              | (none, o1) => (none, o1)
          match combined with
          | (none, o1) => .ok (.float ft .poison, o1)
          | (some (raw, nanInputs), o2) =>
            match handleFMF fmf false false raw with
            | .poison => .ok (.float ft .poison, o2)
            | .value r =>
              let flushed := handleDenormal cfg.denormalMode.output false false r
              match nanPropagate cfg.nanMode flushed nanInputs o2 with
              | (fin, o3) => .ok (.float ft (.value fin), o3)
      | _ => .error (.staticError s!"{name} expects a non-empty float vector argument")
  else if strHasPrefix name "llvm.experimental.get.vector.length" then
    -- nondeterministic per LangRef: any value in [ceil(cnt / ceil(cnt / max)), max] when cnt > max
    some <| match argVals, retTy with
      | [.bv _ (.value cntBV), .bv _ (.value vfBV), .bv 1 (.value scBV)], .ret (.int rw) =>
        let mult := if scBV == 1#1 then cfg.vscale else 1
        let maxLanes := vfBV.toNat * mult
        let cnt := cntBV.toNat
        if cnt == 0 then .ok (.bv rw (.value 0), o)
        else if cnt ≤ maxLanes then .ok (.bv rw (.value (BitVec.ofNat rw cnt)), o)
        else
          let iters := (cnt + maxLanes - 1) / maxLanes
          let lower := (cnt + iters - 1) / iters
          let range := maxLanes - lower + 1
          match o.nextNat with
          | (r, o1) =>
            let res := lower + r % range
            if res < 2 ^ 32 then .ok (.bv rw (.value (BitVec.ofNat rw res)), o1)
            else .ok (.bv rw .poison, o1)
      | [_, _, _], .ret (.int rw) => .ok (.bv rw .poison, o)
      | _, _ => .error (.staticError "llvm.experimental.get.vector.length expects (cnt, vf, scalable)")
  else
    (evalPureDetIntrinsic? cfg name retTy fmf argVals).map fun r => r.map (·, o)

end LeanNanoLlvm.Semantics
