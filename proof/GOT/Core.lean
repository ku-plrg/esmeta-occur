set_option linter.unusedVariables false

namespace GOT

abbrev Label := Nat
abbrev Var   := String
abbrev Field := String
abbrev Addr  := Nat

inductive Prim where
  | bool (b : Bool)
  | num  (n : Int)
  | str  (s : String)
deriving Inhabited, DecidableEq

structure Func where
  params : List Var
  entry  : Label
deriving Inhabited, DecidableEq

inductive Ty where
  | lit    (p : Prim)
  | bool
  | num
  | str
  | func   (Λ : Func)
  | record (fs : List (Field × Ty))
  | union  (t₁ t₂ : Ty)
  | inter  (t₁ t₂ : Ty)
  | diff   (t₁ t₂ : Ty)
  | top
  | bot
deriving Inhabited

mutual
  def Ty.beq : Ty → Ty → Bool
    | .lit p, .lit q => decide (p = q)
    | .bool, .bool => true
    | .num, .num => true
    | .str, .str => true
    | .func Λ, .func Λ' => decide (Λ = Λ')
    | .record fs, .record gs => Ty.beqFlds fs gs
    | .union a b, .union c d => a.beq c && b.beq d
    | .inter a b, .inter c d => a.beq c && b.beq d
    | .diff a b, .diff c d => a.beq c && b.beq d
    | .top, .top => true
    | .bot, .bot => true
    | _, _ => false
  def Ty.beqFlds : List (Field × Ty) → List (Field × Ty) → Bool
    | [], [] => true
    | (f, t) :: r, (g, u) :: s => f == g && t.beq u && Ty.beqFlds r s
    | _, _ => false
end

instance : BEq Ty := ⟨Ty.beq⟩

abbrev UnOp  := String
abbrev BinOp := String

inductive Expr where
  | prim      (p : Prim)
  | var       (x : Var)
  | fieldAcc  (e : Expr) (f : Field)
  | unop      (op : UnOp) (e : Expr)
  | binop     (op : BinOp) (e₁ e₂ : Expr)
  | fn        (Λ : Func)
  | typeCheck (e : Expr) (τ : Ty)
deriving Inhabited

inductive Inst where
  | assign   (x : Var) (e : Expr)
  | alloc    (x : Var) (fes : List (Field × Expr))
  | fieldUpd (e₁ : Expr) (f : Field) (e₂ : Expr)
  | branch   (e : Expr) (lThen lElse : Label)
  | assert   (e : Expr)
  | call     (x : Var) (e₀ : Expr) (args : List Expr)
  | ret      (e : Expr)
deriving Inhabited

structure Program where
  func : Label → Option Func
  inst : Label → Option Inst
  next : Label → Option Label

inductive Value where
  | prim    (p : Prim)
  | addr    (a : Addr)
  | funcVal (Λ : Func)
deriving Inhabited

abbrev Record := Field → Option Value
abbrev Heap   := Addr → Option Record
abbrev Env    := Var → Option Value

structure Memory where
  heap : Heap
  env  : Env
deriving Inhabited

def updFn {α β : Type} [DecidableEq α] (g : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else g x

mutual
  inductive CallCtx : Type where
    | eps   : CallCtx
    | frame : ConcState → CallCtx
  inductive ConcState : Type where
    | mk : CallCtx → Label → Memory → ConcState
end

def ConcState.ctx   : ConcState → CallCtx | .mk κ _ _ => κ
def ConcState.label : ConcState → Label  | .mk _ l _ => l
def ConcState.mem   : ConcState → Memory | .mk _ _ m => m

opaque evalUnop  : UnOp → Value → Option Prim
opaque evalBinop : BinOp → Value → Value → Option Prim

mutual
  def typeTest (h : Heap) : Ty → Value → Bool
    | .lit p, v => match v with | .prim q => decide (q = p) | _ => false
    | .bool,  v => match v with | .prim (.bool _) => true | _ => false
    | .num,   v => match v with | .prim (.num _)  => true | _ => false
    | .str,   v => match v with | .prim (.str _)  => true | _ => false
    | .func Λ, v => match v with | .funcVal Λ' => decide (Λ' = Λ) | _ => false
    | .record fs, v =>
        match v with
        | .addr a =>
            match h a with
            | some r => typeTestFlds h fs r
            | none => false
        | _ => false
    | .union t₁ t₂, v => typeTest h t₁ v || typeTest h t₂ v
    | .inter t₁ t₂, v => typeTest h t₁ v && typeTest h t₂ v
    | .diff t₁ t₂,  v => typeTest h t₁ v && !(typeTest h t₂ v)
    | .top, _ => true
    | .bot, _ => false
  def typeTestFlds (h : Heap) : List (Field × Ty) → Record → Bool
    | [], _ => true
    | (f, t) :: rest, r =>
        (match r f with | some w => typeTest h t w | none => false)
          && typeTestFlds h rest r
end

def evalExpr (m : Memory) : Expr → Option Value
  | .prim p => some (.prim p)
  | .var x => m.env x
  | .fieldAcc e f =>
      (evalExpr m e).bind fun v =>
        match v with
        | .addr a => (m.heap a).bind fun r => r f
        | _ => none
  | .unop op e => (evalExpr m e).bind fun v => (evalUnop op v).map Value.prim
  | .binop op e₁ e₂ =>
      (evalExpr m e₁).bind fun v₁ =>
        (evalExpr m e₂).bind fun v₂ => (evalBinop op v₁ v₂).map Value.prim
  | .fn Λ => some (.funcVal Λ)
  | .typeCheck e τ =>
      (evalExpr m e).map fun v => .prim (.bool (typeTest m.heap τ v))

def evalArgs (m : Memory) (es : List Expr) : Option (List Value) :=
  es.mapM (evalExpr m)

def bindParams (xs : List Var) (vs : List Value) : Env :=
  fun x => (xs.zip vs).lookup x

def isTrueV (v : Value) : Prop := v = .prim (.bool true)

inductive Step (P : Program) : ConcState → ConcState → Prop where
  | assign {κ : CallCtx} {l : Label} {m : Memory} {x : Var} {e : Expr}
      {v : Value} {l' : Label} :
      P.inst l = some (.assign x e) →
      evalExpr m e = some v →
      P.next l = some l' →
      Step P (.mk κ l m) (.mk κ l' ⟨m.heap, updFn m.env x (some v)⟩)
  | alloc {κ : CallCtx} {l : Label} {m : Memory} {x : Var}
      {fes : List (Field × Expr)} {fvs : List (Field × Value)}
      {a : Addr} {l' : Label} :
      P.inst l = some (.alloc x fes) →
      fes.mapM (fun fe => (evalExpr m fe.2).map (fun v => (fe.1, v))) = some fvs →
      m.heap a = none →
      P.next l = some l' →
      Step P (.mk κ l m)
        (.mk κ l' ⟨updFn m.heap a (some (fun f => fvs.lookup f)),
                   updFn m.env x (some (.addr a))⟩)
  | fieldUpd {κ : CallCtx} {l : Label} {m : Memory} {e₁ : Expr} {f : Field}
      {e₂ : Expr} {a : Addr} {r : Record} {v : Value} {l' : Label} :
      P.inst l = some (.fieldUpd e₁ f e₂) →
      evalExpr m e₁ = some (.addr a) →
      m.heap a = some r →
      evalExpr m e₂ = some v →
      P.next l = some l' →
      Step P (.mk κ l m)
        (.mk κ l' ⟨updFn m.heap a (some (updFn r f (some v))), m.env⟩)
  | branchT {κ : CallCtx} {l : Label} {m : Memory} {e : Expr}
      {lt lf : Label} {v : Value} :
      P.inst l = some (.branch e lt lf) →
      evalExpr m e = some v → isTrueV v →
      Step P (.mk κ l m) (.mk κ lt m)
  | branchF {κ : CallCtx} {l : Label} {m : Memory} {e : Expr}
      {lt lf : Label} {v : Value} :
      P.inst l = some (.branch e lt lf) →
      evalExpr m e = some v → ¬ isTrueV v →
      Step P (.mk κ l m) (.mk κ lf m)
  | assert {κ : CallCtx} {l : Label} {m : Memory} {e : Expr}
      {v : Value} {l' : Label} :
      P.inst l = some (.assert e) →
      evalExpr m e = some v → isTrueV v →
      P.next l = some l' →
      Step P (.mk κ l m) (.mk κ l' m)
  | call {κ : CallCtx} {l : Label} {m : Memory} {x : Var} {e₀ : Expr}
      {args : List Expr} {Λ : Func} {vs : List Value} :
      P.inst l = some (.call x e₀ args) →
      evalExpr m e₀ = some (.funcVal Λ) →
      evalArgs m args = some vs →
      Step P (.mk κ l m)
        (.mk (.frame (.mk κ l m)) Λ.entry ⟨m.heap, bindParams Λ.params vs⟩)
  | ret {κ' : CallCtx} {lc : Label} {mc : Memory} {l : Label} {m : Memory}
      {e : Expr} {v : Value} {x : Var} {e₀ : Expr} {args : List Expr}
      {lc' : Label} :
      P.inst l = some (.ret e) →
      evalExpr m e = some v →
      P.inst lc = some (.call x e₀ args) →
      P.next lc = some lc' →
      Step P (.mk (.frame (.mk κ' lc mc)) l m)
             (.mk κ' lc' ⟨m.heap, updFn mc.env x (some v)⟩)

inductive Reach (P : Program) (σ₀ : ConcState) : ConcState → Prop where
  | refl : Reach P σ₀ σ₀
  | tail {σ σ' : ConcState} : Reach P σ₀ σ → Step P σ σ' → Reach P σ₀ σ'

mutual
  def gammaTy : Ty → Heap → Value → Prop
    | .lit p,        _, v => v = .prim p
    | .bool,         _, v => ∃ b, v = .prim (.bool b)
    | .num,          _, v => ∃ n, v = .prim (.num n)
    | .str,          _, v => ∃ s, v = .prim (.str s)
    | .func Λ,       _, v => v = .funcVal Λ
    | .record fs,    h, v => ∃ a r, v = .addr a ∧ h a = some r ∧ gammaFlds fs h r
    | .union t₁ t₂,  h, v => gammaTy t₁ h v ∨ gammaTy t₂ h v
    | .inter t₁ t₂,  h, v => gammaTy t₁ h v ∧ gammaTy t₂ h v
    | .diff t₁ t₂,   h, v => gammaTy t₁ h v ∧ ¬ gammaTy t₂ h v
    | .top,          _, _ => True
    | .bot,          _, _ => False
  def gammaFlds : List (Field × Ty) → Heap → Record → Prop
    | [],             _, _ => True
    | (f, t) :: rest, h, r =>
        (∃ w, r f = some w ∧ gammaTy t h w) ∧ gammaFlds rest h r
end

def Subty (t₁ t₂ : Ty) : Prop :=
  ∀ h v, gammaTy t₁ h v → gammaTy t₂ h v

def heapField (h : Heap) (a : Addr) (f : Field) : Option Value :=
  (h a).bind fun r => r f

def HeapEvolves (δ : Field → Option Ty) (h₀ h : Heap) : Prop :=
  ∀ a, h₀ a ≠ none →
    h a ≠ none ∧
    ∀ f, heapField h a f ≠ heapField h₀ a f →
      ∃ τ v, δ f = some τ ∧ heapField h a f = some v ∧ gammaTy τ h v

end GOT
