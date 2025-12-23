import HTPILib.HTPIDefs
namespace HTPI

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  have h4 : Q → R := h h3
  contrapos at h4            --Now h4 : ¬R → ¬Q
  show ¬Q from h4 h2
  done


theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
    contrapos
    assume h3: P
    have h4:=h1 h3
    show ¬R from h2 h4
    done


def predOrZero : Nat → Nat
| 0 => 0
| Nat.succ n => n

#eval predOrZero 3

def xor : Bool × Bool->Bool
| (true, true) => false
| (false ,false) => false
| (false, true) => true
| (true ,false) => true

#eval xor (true,true)


def length {α:Type } : List α -> Nat
| [] => 0
| _ :: xs => (length xs) + 1

#eval length [10,20,30]

def append {α : Type} : List α → List α → List α
| [], ys => ys
| x :: xs, ys => x :: append xs ys

#eval append ([1,2]:List Nat) [3,4]

def snoc {α: Type}: List α → α → List α
| [], a => [a]
| x::xs, a => x::(snoc xs a)

#eval snoc [1,2,3,4] 5

def revAux {α : Type} : List α → List α → List α
| [], acc => acc
| x :: xs, acc => revAux xs (x::acc)

def reverse {α : Type} (xs : List α) : List α :=
  revAux xs []

#eval reverse [1,2,3,4]


-- λfirst. λsecond. first
def selectFirst : α → β → α :=
  fun first => fun second => first

example (argument1 : α) (argument2 : β) :
    selectFirst argument1 argument2 = argument1 := by
  unfold selectFirst
  -- goal is now: (fun first => fun second => first) argument1 argument2 = argument1
  dsimp


end HTPI
