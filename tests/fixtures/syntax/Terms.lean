prelude

def app := fun (f : A) (a : A) => f a
def compose := fun (f : B) (g : A) => fun a => f (g a)
def fa := ∀ (x : A) {y : B} [inst : C] ⦃z : D⦄, E
def lam2 := fun (a : A) {b : B} => a
def lamMatch := fun | y => y
def letTerm := let x := f a; g x
def matchTerm := fun n m => match n, m with
  | c, _ => c
  | _, d => d
def structTerm := { field := a, other := b }
def structUpdate := fun s => { s with field := a }
def projections := fun s => s.field.1.2
def ascription := (a : A)
def tuple := (a, b, c)
def unit' := ()
def anon := ⟨a, b⟩
def anonEmpty := ⟨⟩
def explicitApp := @f A a
def holes := (_ : A)
def synth := (?_ : A)
def sorts := fun (α : Sort 1) (β : Type 2) (γ : Prop) => γ
def uni := fun (α : Sort u) (β : Sort (max u v)) (δ : Sort (imax u v)) => Sort _
def arrowChain := fun (f : A) (a : A) => f a
def haveTerm := have h := a; h
def showTerm := show A from a
def sufficesTerm := suffices h : A from a; h
def depArrowT := fun (f : (x : A) → B) => f
def sorryTerm := sorry
def omissionTerm := ⋯
def inaccessibleTerm := fun p => match p with
  | .(a) => a
def unsafeTerm := unsafe a
def explicitUnivT := f.{u, v}
def letTyped := let x : A := a; x
def funTyped := fun x : A => x
