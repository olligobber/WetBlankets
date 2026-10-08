import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import WetBlankets.Puzzle

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

lemma col_three_neg : ⟨3, 2⟩ ∈ negs ∨ ⟨3, 3⟩ ∈ negs := by
  obtain ⟨r, hr⟩ := col_has_neg 3
  have in_cage_cell := all_neg_in_cage_cells hr
  let valid_set : Finset Cell := cage_cells.filter (·.col = 3)
  have in_valid : ⟨3, r⟩ ∈ valid_set := by
    simp only [Finset.mem_filter, and_true, valid_set]
    exact in_cage_cell
  simp only
    [show valid_set = {⟨3, 2⟩, ⟨3, 3⟩} by decide
    , Finset.mem_insert
    , Cell.mk.injEq
    , true_and
    , Finset.mem_singleton
    ] at in_valid
  obtain h | h := in_valid <;> cases h <;> simp[hr]

lemma neg_x_wing_one : {⟨3, 2⟩, ⟨7, 3⟩} ⊆ negs ∨ {⟨3, 3⟩, ⟨7, 2⟩} ⊆ negs := by
  obtain h₁ | h₁ := col_seven_neg <;>
    obtain h₂ | h₂ := col_three_neg <;>
    simp[Finset.subset_iff, h₁, h₂] <;>
    have h₃ := validsol.2.2.2.2.2.1 _ h₁ _ h₂ (by decide) <;>
    simp at h₃

theorem l_neg : ⟨0, 4⟩ ∈ negs := by
  obtain ⟨cage, cage_cells⟩ :
    ∃ cage : cages, cage.val.cells = { ⟨0, 3⟩, ⟨0, 4⟩ } := by decide
  obtain ⟨cell, cell_in_cage, cell_is_neg⟩ := cage_has_some_neg cage cage.prop
  simp only
    [ cage_cells
    , Finset.mem_insert
    , Finset.mem_singleton
    ] at cell_in_cage
  obtain h | h := cell_in_cage <;> cases h <;> try exact cell_is_neg
  obtain h | h := neg_x_wing_one <;>
    simp only
      [ Finset.subset_iff
      , Finset.mem_insert
      , Finset.mem_singleton
      , forall_eq_or_imp
      , forall_eq
      ] at h <;>
    obtain ⟨h₁, h₂⟩ := h
  · have := validsol.2.2.2.2.2.1 _ cell_is_neg _ h₂ (by decide)
    simp at this
  · have := validsol.2.2.2.2.2.1 _ cell_is_neg _ h₁ (by decide)
    simp at this

theorem c_neg : ⟨5, 5⟩ ∈ negs := by
  obtain ⟨cage, cage_cells⟩ :
    ∃ cage : cages,
      cage.val.cells = { ⟨4, 4⟩, ⟨5, 4⟩, ⟨6, 4⟩, ⟨5, 5⟩ }
      := by decide
  obtain ⟨⟨c, r⟩, cell_in_cage, cell_is_neg⟩ := cage_has_some_neg cage cage.prop
  have c_not_zero : c ≠ 0 := fun h ↦ by simp
    [ h
    , cage_cells
    , show (0 : Col) ≠ 4 by decide
    , show (0 : Col) ≠ 5 by decide
    , show (0 : Col) ≠ 6 by decide
    ] at cell_in_cage
  have r_not_four : r ≠ 4 := by
    have := validsol.2.2.2.2.2.1 _ cell_is_neg _ l_neg (by simp[c_not_zero])
    simp only [ne_eq] at this
    exact this.1
  let valid_set := cage.val.cells.filter (·.row ≠ 4)
  have : ⟨c, r⟩ ∈ valid_set := by
    simp[valid_set, cell_in_cage, r_not_four]
  simp only
    [ne_eq
    , cage_cells
    , Finset.mem_filter
    , Finset.mem_insert
    , Cell.mk.injEq
    , r_not_four
    , and_false
    , Finset.mem_singleton
    , false_or
    , not_false_eq_true
    , and_true
    , valid_set
    ] at this
  cases this.1
  cases this.2
  exact cell_is_neg

theorem t_neg : ⟨3, 2⟩ ∈ negs := by
  obtain h | h := neg_x_wing_one <;>
    simp only
      [ Finset.subset_iff
      , Finset.mem_insert
      , forall_eq_or_imp
      ] at h
  · exact h.1
  · obtain ⟨h, _⟩ := h
    have := validsol.2.2.2.2.2.1 _ h _ c_neg (by decide)
    simp only
      [ show Cell.box ⟨3, 3⟩ = Cell.box ⟨5, 5⟩ by decide
      , ne_eq
      , not_true_eq_false
      , false_and
      , and_false
      ] at this

theorem r_neg : ⟨7, 3⟩ ∈ negs := by
  obtain h | h := neg_x_wing_one <;>
    simp only
      [ Finset.subset_iff
      , Finset.mem_insert
      , Finset.mem_singleton
      , forall_eq_or_imp
      , forall_eq
      ] at h
  · exact h.2
  · obtain ⟨h, _⟩ := h
    have := validsol.2.2.2.2.2.1 _ h _ t_neg (by decide)
    simp at this
