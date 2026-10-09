import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic

structure Row : Type where
  toFin : Fin 9

instance {x : Nat} [OfNat (Fin 9) x] : OfNat Row x where
  ofNat := ⟨OfNat.ofNat x⟩

structure Col : Type where
  toFin : Fin 9

instance {x : Nat} [OfNat (Fin 9) x] : OfNat Col x where
  ofNat := ⟨OfNat.ofNat x⟩

structure Cell : Type where
  col : Col
  row : Row

structure Box : Type where
  toFin : Fin 9

instance {x : Nat} [OfNat (Fin 9) x] : OfNat Box x where
  ofNat := ⟨OfNat.ofNat x⟩

def Cell.box : Cell → Box := fun cell ↦ by
  constructor
  refine ⟨cell.row.toFin / 3 * 3 + cell.col.toFin / 3, ?_⟩
  have h₁ : ∀ x : Fin 9, x.val / 3 ≤ 2 := by
    intro x
    have h₁ := x.isLt
    rw[Nat.lt_succ_iff] at h₁
    have h₂ := @Nat.div_le_div x.val 8 3 3 h₁ (by simp) (by simp)
    simp only [Nat.reduceDiv] at h₂
    exact h₂
  have h₂ : cell.row.toFin.val / 3 * 3 ≤ 6 := by
    have := Nat.mul_le_mul_right 3 <| h₁ cell.row.toFin
    simp only [Nat.reduceMul] at this
    exact this
  have h₃ := h₁ cell.col.toFin
  rw[Nat.lt_succ_iff]
  exact Nat.add_le_add h₂ h₃

structure Digit : Type where
  val : Nat
  nonzero : val > 0
  single : val < 10

instance {n : Nat} [NeZero n] : OfNat Digit n where
  ofNat := by
    refine ⟨(n - 1) % 9 + 1, by simp, ?_⟩
    apply Nat.add_lt_add_right
    exact Nat.mod_lt (n - 1) (by decide)

deriving instance DecidableEq for
  Row,
  Col,
  Cell,
  Box,
  Digit

instance : Fintype Row where
  elems := Finset.image Row.mk Fintype.elems
  complete := by
    intro ⟨n⟩
    have := @Fintype.complete (Fin 9) _ n
    rw [Finset.mem_image]
    use n

instance : Fintype Col where
  elems := Finset.image Col.mk Fintype.elems
  complete := by
    intro ⟨n⟩
    have := @Fintype.complete (Fin 9) _ n
    rw [Finset.mem_image]
    use n

def Solution : Type := Cell → Digit

class Rule (t : Type) where
  satisfies : t → Solution → Prop

structure StandardSudoku : Type where

instance StandardSudoku.rule : Rule StandardSudoku where
  satisfies _ sol :=
    ∀ c : Cell, ∀ d : Cell,
    c ≠ d →
    c.row = d.row ∨ c.col = d.col ∨ c.box = d.box →
      sol c ≠ sol d

structure VSum : Type where
  cell1 : Cell
  cell2 : Cell

instance VSum.rule : Rule VSum where
  satisfies vsum sol :=
    (sol vsum.cell1).val + (sol vsum.cell2).val = 5

structure XSum : Type where
  cell1 : Cell
  cell2 : Cell

instance XSum.rule : Rule XSum where
  satisfies xsum sol :=
    (sol xsum.cell1).val + (sol xsum.cell2).val = 10

structure BlackKropki : Type where
  cell1 : Cell
  cell2 : Cell

instance BlackKropki.rule : Rule BlackKropki where
  satisfies dot sol :=
    (sol dot.cell1).val = (sol dot.cell2).val * 2 ∨
    (sol dot.cell2).val = (sol dot.cell1).val * 2

structure GreyCircle : Type where
  cell : Cell

instance GreyCircle.rule : Rule GreyCircle where
  satisfies circle sol :=
    (sol circle.cell).val % 2 = 1

structure NegSolution where
  negcells : Finset Cell
  digit : Solution

def NegSolution.value : NegSolution → Cell → Int := fun sol cell ↦
  if cell ∈ sol.negcells then
    - (sol.digit cell).val
  else
    (sol.digit cell).val

class NegRule (t : Type) where
  satisfies : t → NegSolution → Prop

-- instance {t : Type} [Rule t] : NegRule t where
--   satisfies r sol := Rule.satisfies r sol.digit

structure NegRepeats : Type where

instance NegRepeats.rule : NegRule NegRepeats where
  satisfies _ sol :=
    ∀ c ∈ sol.negcells, ∀ d ∈ sol.negcells, c ≠ d →
      c.row ≠ d.row ∧
      c.col ≠ d.col ∧
      c.box ≠ d.box ∧
      sol.digit c ≠ sol.digit d

structure KillerCage : Type where
  cells : Finset Cell
  total : Option Int

instance KillerCage.rule : NegRule KillerCage where
  satisfies cage sol :=
    cage.total.all (∑ x ∈ cage.cells, sol.value x = ·) ∧
    ∃ c ∈ cage.cells,
      c ∈ sol.negcells ∧
      ∀ d ∈ cage.cells, c ≠ d → d ∉ sol.negcells

deriving instance DecidableEq for
  VSum,
  XSum,
  BlackKropki,
  GreyCircle,
  KillerCage

structure Puzzle : Type where
  vsums : Finset VSum
  xsums : Finset XSum
  blackkropkis : Finset BlackKropki
  greycircles : Finset GreyCircle
  killercages : Finset KillerCage

instance : NegRule Puzzle where
  satisfies puzzle sol :=
    Rule.satisfies StandardSudoku.mk sol.digit ∧
    (∀ vsum ∈ puzzle.vsums, Rule.satisfies vsum sol.digit) ∧
    (∀ xsum ∈ puzzle.xsums, Rule.satisfies xsum sol.digit) ∧
    (∀ dot ∈ puzzle.blackkropkis, Rule.satisfies dot sol.digit) ∧
    (∀ circle ∈ puzzle.greycircles, Rule.satisfies circle sol.digit) ∧
    NegRule.satisfies NegRepeats.mk sol ∧
    ∀ cage ∈ puzzle.killercages, NegRule.satisfies cage sol

def wet_blankets : Puzzle where
  vsums := { ⟨⟨5, 6⟩, ⟨5, 7⟩⟩ }
  xsums := { ⟨⟨1, 2⟩, ⟨1, 3⟩⟩ }
  blackkropkis :=
    { ⟨⟨0, 0⟩, ⟨0, 1⟩⟩
    , ⟨⟨1, 3⟩, ⟨1, 4⟩⟩
    , ⟨⟨3, 3⟩, ⟨4, 3⟩⟩
    , ⟨⟨4, 6⟩, ⟨4, 7⟩⟩
    }
  greycircles := { ⟨4, 3⟩ }
  killercages :=
    { ⟨ { ⟨2, 0⟩
        , ⟨2, 1⟩
        , ⟨2, 2⟩
        }
      , some 4
      ⟩
    , ⟨ { ⟨0, 3⟩
        , ⟨0, 4⟩
        }
      , some 8
      ⟩
    , ⟨ { ⟨0, 7⟩
        , ⟨0, 8⟩
        , ⟨1, 7⟩
        , ⟨1, 8⟩
        }
      , some (-3)
      ⟩
    , ⟨ { ⟨2, 3⟩
        , ⟨3, 3⟩
        , ⟨3, 2⟩
        }
      , some 2
      ⟩
    , ⟨ { ⟨4, 4⟩
        , ⟨5, 4⟩
        , ⟨5, 5⟩
        , ⟨6, 4⟩
        }
      , some 10
      ⟩
    , ⟨ { ⟨4, 7⟩
        , ⟨4, 8⟩
        , ⟨5, 8⟩
        , ⟨6, 8⟩
        }
      , some 0
      ⟩
    , ⟨ { ⟨5, 1⟩
        , ⟨5, 2⟩
        , ⟨6, 0⟩
        , ⟨6, 1⟩
        , ⟨6, 2⟩
        }
      , some 15
      ⟩
    , ⟨ { ⟨5, 3⟩
        , ⟨6, 3⟩
        , ⟨7, 3⟩
        , ⟨7, 2⟩
        }
      , some 18
      ⟩
    , ⟨ { ⟨8, 6⟩ }
      , none
      ⟩
    }

axiom solution : NegSolution
axiom validsol : NegRule.satisfies wet_blankets solution
