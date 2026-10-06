import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Union

-- https://sudokupad.app/tdzmfngyfp

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
    0 - (sol.digit cell).val
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
    cage.total.all (cage.cells.sum sol.value = ·) ∧
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

def cages := wet_blankets.killercages
noncomputable def negs := solution.negcells

theorem br_neg : ⟨8, 6⟩ ∈ negs := by
  have ⟨cage, cageinpuzzle, cageset⟩ :
    ∃ cage ∈ cages, cage.cells = { ⟨8, 6⟩ } := by
      decide
  have ⟨cell, cellincage, cellneg, _⟩ :=
    (validsol.2.2.2.2.2.2 cage cageinpuzzle).2
  rw[cageset, Finset.mem_singleton] at cellincage
  cases cellincage
  exact cellneg

lemma cage_has_some_neg : ∀ cage ∈ cages, ∃ cell ∈ cage.cells, cell ∈ negs := by
  intro cage hcage
  have ⟨cell, cellincage, cellisneg, _⟩ := (validsol.2.2.2.2.2.2 cage hcage).2
  exact ⟨cell, cellincage, cellisneg⟩

noncomputable def cage_neg : (cage : cages) → negs := fun ⟨cage, hcage⟩ ↦
  ⟨ (cage_has_some_neg cage hcage).choose
  , (cage_has_some_neg cage hcage).choose_spec.2
  ⟩

lemma cage_has_neg : ∀ cage : cages, (cage_neg cage).val ∈ cage.val.cells :=
  fun ⟨cage, hcage⟩ ↦ (cage_has_some_neg cage hcage).choose_spec.1

lemma cage_neg_inj : Function.Injective cage_neg := by
  have disjoint_cages :
    ∀ c ∈ cages, ∀ d ∈ cages,
    c ≠ d → c.cells ∩ d.cells = ∅ := by decide
  intro cage dage h
  let cell := cage_neg cage
  have cell_in_cage := cage_has_neg cage
  change cell.val ∈ cage.val.cells at cell_in_cage
  have cell_in_dage : cell.val ∈ dage.val.cells := by
    change (cage_neg cage).val ∈ dage.val.cells
    rw[h]
    exact cage_has_neg dage
  have cell_in_inter : cell.val ∈ cage.val.cells ∩ dage.val.cells := by
    rw[Finset.mem_inter]
    exact ⟨cell_in_cage, cell_in_dage⟩
  by_contra neq
  rw[Subtype.mk.injEq] at neq
  have disjoint := disjoint_cages cage cage.prop dage dage.prop neq
  rw[disjoint] at cell_in_inter
  simp at cell_in_inter

lemma nine_negs : negs.card = 9 := by
  have atleast_nine : negs.card ≥ 9 := by
    let cages := wet_blankets.killercages
    have nine_cages : cages.card = 9 := by decide
    let cage_cells := cages.attach.map ⟨cage_neg, cage_neg_inj⟩
    have nine_cage_cells : cage_cells.card = 9 :=
      Finset.card_map ⟨cage_neg, cage_neg_inj⟩
    change 9 ≤ negs.card
    rw[← Finset.card_attach, Finset.le_card_iff_exists_subset_card]
    refine ⟨cage_cells, ?_, nine_cage_cells⟩
    intro cell _
    simp
  have atmost_nine : negs.card ≤ 9 := by
    let negcell_row : negs → Fin 9 := fun ⟨cell, _⟩ ↦ cell.row.toFin
    have row_injective : Function.Injective negcell_row := by
      intro ⟨cell, hcell⟩ ⟨dell, hdell⟩ h
      change cell.row.toFin = dell.row.toFin at h
      rw[←Row.mk.injEq] at h
      change cell.row = dell.row at h
      rw[Subtype.mk.injEq]
      by_contra neq
      exact (validsol.2.2.2.2.2.1 cell hcell dell hdell neq).1 h
    let negcell_rows := negs.attach.map ⟨negcell_row, row_injective⟩
    have : negcell_rows.card = negs.attach.card :=
      Finset.card_map ⟨negcell_row, row_injective⟩
    rw[Finset.card_attach] at this
    rw[← this]
    let univ_nine : Finset (Fin 9) := Finset.univ
    have : univ_nine.card = 9 := by decide
    conv =>
      rhs
      rw[← this]
    rw[Finset.le_card_iff_exists_subset_card]
    use negcell_rows
    simp only [and_true]
    exact Finset.subset_univ negcell_rows
  exact le_antisymm atmost_nine atleast_nine

lemma col_has_neg : ∀ c : Col, ∃ r : Row, ⟨c, r⟩ ∈ negs := by
  intro col
  let neg_col : (c : Cell) → c ∈ solution.negcells → Col :=
    fun cell _ ↦ cell.col
  have neg_col_inj :
    ∀ (cell dell : Cell) (hc : cell ∈ negs) (hd : dell ∈ negs),
      neg_col cell hc = neg_col dell hd → cell = dell := by
        intro cell dell hc hd h₁
        change cell.col = dell.col at h₁
        by_contra h₂
        exact (validsol.2.2.2.2.2.1 cell hc dell hd h₂).2.1 h₁
  obtain ⟨cell, h₃, h₄⟩ := @Finset.surj_on_of_inj_on_of_card_le
    Cell
    Col
    negs
    Finset.univ
    neg_col
    (by simp)
    neg_col_inj
    (by
      rw[nine_negs]
      decide
    )
    col
    (by simp)
  use cell.row
  rw[h₄]
  exact h₃

lemma all_neg_in_cage : ∀ cell ∈ negs, ∃ cage ∈ cages, cell ∈ cage.cells := by
  intro cell is_neg
  obtain ⟨cage, _, hcell⟩ := @Finset.surj_on_of_inj_on_of_card_le
    cages
    negs
    Finset.univ
    Finset.univ
    (fun cage _ ↦ cage_neg cage)
    (by simp)
    (fun cage dage _ _ h ↦ cage_neg_inj h)
    (by
      rw[Finset.univ_eq_attach, Finset.card_attach, nine_negs]
      decide
    )
    ⟨cell, is_neg⟩
    (by simp)
  refine ⟨cage, cage.prop, ?_⟩
  have := cage_has_neg cage
  rw[← hcell] at this
  exact this

def cage_cells : Finset Cell := cages.biUnion (·.cells)

lemma all_neg_in_cage_cells : negs ⊆ cage_cells := by
  intro cell hcell
  change cell ∈ cages.biUnion (·.cells)
  rw[Finset.mem_biUnion]
  exact all_neg_in_cage cell hcell

lemma col_seven_neg : ⟨7, 2⟩ ∈ negs ∨ ⟨7, 3⟩ ∈ negs := by
  obtain ⟨r, hr⟩ := col_has_neg 7
  have in_cage_cell := all_neg_in_cage_cells hr
  let valid_set : Finset Cell := cage_cells.filter (·.col = 7)
  have in_valid : ⟨7, r⟩ ∈ valid_set := by
    simp only [Finset.mem_filter, and_true, valid_set]
    exact in_cage_cell
  simp only
    [show valid_set = {⟨7, 2⟩, ⟨7, 3⟩} by decide
    , Finset.mem_insert
    , Cell.mk.injEq
    , true_and
    , Finset.mem_singleton
    ] at in_valid
  obtain h | h := in_valid <;> cases h <;> simp[hr]
