import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import WetBlankets.Puzzle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Defs.LinearOrder

def cages := wet_blankets.killercages
noncomputable def negs := solution.negcells
noncomputable def digit := solution.digit
noncomputable def int_digit : Cell → ℤ := fun cell ↦ ↑(digit cell).val

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

lemma digit_val_of_nat {n : Nat} [h₁ : NeZero n] (h₂ : n < 10) :
  Digit.val (OfNat.ofNat n) = n := by
    change (n - 1) % 9 + 1 = n
    rw[Nat.mod_eq_of_lt (by omega)]
    rw[Nat.sub_one_add_one h₁.out]

lemma l_cage_sum : ↑(digit ⟨0, 3⟩).val - ↑(digit ⟨0, 4⟩).val = (8 : ℤ) := by
  let cage : KillerCage := ⟨{⟨0, 3⟩, ⟨0, 4⟩}, some 8⟩
  have hcage : cage ∈ cages := by decide
  have non_neg : ⟨0, 3⟩ ∉ negs := by
    by_contra h
    have := validsol.2.2.2.2.2.1 _ h _ l_neg (by decide)
    simp at this
  have sum_cage := (validsol.2.2.2.2.2.2 cage hcage).1
  simp only [Option.all_some, decide_eq_true_eq, cage] at sum_cage
  rw[Finset.sum_pair (by decide)] at sum_cage
  unfold NegSolution.value at sum_cage
  rw[← negs, ← digit] at sum_cage
  simp only [non_neg, ↓reduceIte, l_neg] at sum_cage
  exact sum_cage

theorem digit04 : digit ⟨0, 4⟩ = 1 := by
  have sum_cage := l_cage_sum
  have ub : (↑(digit ⟨0, 3⟩).val : ℤ) < 10 := by
    have := (digit ⟨0, 3⟩).single
    rw[← @Nat.cast_lt ℤ] at this
    exact this
  rw[sub_eq_iff_eq_add] at sum_cage
  simp only [sum_cage] at ub
  rw[show (10 : ℤ) = 8 + 2 by decide, Int.add_lt_add_iff_left] at ub
  simp at ub
  let a := (digit ⟨0, 4⟩).val
  have lb : a > 0 := (digit ⟨0, 4⟩).nonzero
  rw[Digit.mk.injEq, digit_val_of_nat (by decide)]
  change a = 1
  omega

theorem digit03 : digit ⟨0, 3⟩ = 9 := by
  have sum_cage := l_cage_sum
  simp only
    [digit04
    , show Digit.val 1 = 1 by decide
    , Nat.cast_one
    , sub_eq_iff_eq_add
    , Int.reduceAdd
    ] at sum_cage
  rw[Digit.mk.injEq, digit_val_of_nat (by decide)]
  rw[← @Nat.cast_ofNat ℤ 9, Nat.cast_inj] at sum_cage
  exact sum_cage

lemma col_one_neg : ⟨1, 7⟩ ∈ negs ∨ ⟨1, 8⟩ ∈ negs := by
  obtain ⟨r, hr⟩ := col_has_neg 1
  have in_cage_cell := all_neg_in_cage_cells hr
  let valid_set : Finset Cell := cage_cells.filter (·.col = 1)
  have in_valid : ⟨1, r⟩ ∈ valid_set := by
    simp only [Finset.mem_filter, and_true, valid_set]
    exact in_cage_cell
  simp only
    [show valid_set = {⟨1, 7⟩, ⟨1, 8⟩} by decide
    , Finset.mem_insert
    , Cell.mk.injEq
    , true_and
    , Finset.mem_singleton
    ] at in_valid
  obtain h | h := in_valid <;> cases h <;> simp[hr]

lemma cage_total_pos_minus_neg : ∀ cage : cages, cage.val.total.all
  ( (cage.val.cells.erase (cage_neg cage)).sum int_digit -
    int_digit (cage_neg cage) =
    ·) := by
  intro ⟨⟨cage_cells, cage_total⟩, in_puzzle⟩
  cases cage_total <;>
    simp only [Option.all_none, Option.all_some, decide_eq_true_eq]
  rename_i cage_total
  have ⟨is_total, unique_neg⟩ :=
    validsol.2.2.2.2.2.2 ⟨cage_cells, some cage_total⟩ in_puzzle
  obtain ⟨neg_cell, neg_in_cage, neg_is_neg, unique_neg⟩ := unique_neg
  simp only at neg_in_cage
  have neg_cell_is_cage_neg :
    neg_cell = cage_neg ⟨⟨cage_cells, cage_total⟩, in_puzzle⟩ := by
      by_contra h
      exact unique_neg
        (cage_neg ⟨⟨cage_cells, cage_total⟩, in_puzzle⟩)
        (cage_has_neg ⟨⟨cage_cells, cage_total⟩, in_puzzle⟩)
        h
        (cage_neg ⟨⟨cage_cells, cage_total⟩, in_puzzle⟩).prop
  rw[← neg_cell_is_cage_neg]
  simp only [Option.all_some, decide_eq_true_eq] at is_total
  rw
    [ ← Finset.add_sum_erase _ _ neg_in_cage
    , NegSolution.value
    , ← digit
    , ← int_digit
    ] at is_total
  simp only [neg_is_neg, ↓reduceIte] at is_total
  conv at is_total =>
    lhs
    rhs
    rhs
    intro
    rw [NegSolution.value, ← digit, ← int_digit]
  have erase_not_neg :
    ∀ x ∈ cage_cells.erase neg_cell, x ∉ solution.negcells := by
      intro cell cell_in_erase cell_is_neg
      simp only [Finset.mem_erase, ne_eq] at cell_in_erase
      obtain ⟨cell_not_neg, cell_in_cage⟩ := cell_in_erase
      change cell ≠ neg_cell at cell_not_neg
      symm at cell_not_neg
      exact unique_neg cell cell_in_cage cell_not_neg cell_is_neg
  rw[Finset.sum_ite_of_false erase_not_neg] at is_total
  rw[Int.sub_eq_add_neg, Int.add_comm]
  exact is_total

-- Note that `decide` does not like merge sort,
-- so use `decide_cbv` or `native_decide` instead
def take_min {t : Type} [LinearOrder t] : ℕ → Multiset t → Multiset t
  | n, s => s.sort.take n

-- Note that `decide` does not like merge sort,
-- so use `decide_cbv` or `native_decide` instead
def take_max {t : Type} [LinearOrder t] : ℕ → Multiset t → Multiset t
  | n, s => s.sort.reverse.take n

lemma take_min_le {t : Type} [LinearOrder t] {n : ℕ} {s : Multiset t} :
  take_min n s ≤ s := by
    conv =>
      rhs
      rw[← Multiset.sort_eq s LE.le]
    unfold take_min
    simp only
    rw[Multiset.coe_le]
    refine ⟨_, by rfl, ?_⟩
    apply List.take_sublist

@[simp]
lemma take_min_card {t : Type} [LinearOrder t] {n : ℕ} {s : Multiset t}
  (h : n ≤ s.card) : (take_min n s).card = n := by
    unfold take_min
    simp[h]


lemma sum_min_superset_le_sum {t : Type} [LinearOrder t] [AddCommMonoid t]
   [IsOrderedAddMonoid t] :
    ∀ (set superset : Multiset t) (_ : set ≤ superset),
      (take_min set.card superset).sum ≤ set.sum := by
  have : ∀ (n : ℕ) (set superset : Multiset t) (h₁ : set.card = n)
    (h₂ : set ≤ superset), (take_min n superset).sum ≤ set.sum := fun n ↦ by
      induction n with
      | zero =>
        intro set superset h _
        simp only [Multiset.card_eq_zero] at h
        cases h
        unfold take_min
        simp
      | succ n ih =>
        intro set superset h₁ h₂
        let set_sort := set.sort
        have set_nonempty : set.toFinset.Nonempty := by
          simp only [Multiset.toFinset_nonempty]
          intro h
          cases h
          simp at h₁
        let max_set : t := set.toFinset.max' set_nonempty
        have max_set_in_set : max_set ∈ set := by
          have := Finset.max'_mem set.toFinset set_nonempty
          simp only [Multiset.mem_toFinset] at this
          exact this
        let small_set := set.erase max_set
        have set_eq_max_plus_set :=
          Multiset.add_singleton_eq_iff.mpr ⟨max_set_in_set, rfl⟩
        have small_set_card : small_set.card = n := by
          rw[← set_eq_max_plus_set] at h₁
          simp only
            [ Multiset.card_add
            , Multiset.card_singleton
            , Nat.add_right_cancel_iff
            ] at h₁
          exact h₁
        have small_set_in_superset : small_set ≤ superset := by
          trans set
          · exact Multiset.erase_le _ _
          · exact h₂
        have small_set_sum :=
          ih small_set superset small_set_card small_set_in_superset
        rw[← set_eq_max_plus_set]
        unfold take_min
        simp only
          [ Multiset.sum_coe
          , Multiset.sum_add
          , Multiset.sum_singleton
          , ge_iff_le
          ]
        rw
          [ List.take_succ_eq_append_getElem (by
            simp only [Multiset.length_sort]
            apply Nat.lt_of_succ_le
            simp only [Nat.succ_eq_add_one, ← h₁]
            exact Multiset.card_le_card h₂
          )
          , List.sum_append
          ]
        apply add_le_add small_set_sum
        simp only [List.sum_cons, List.sum_nil, add_zero]
        have max_last_sorted : set.sort[n]'(by simp[h₁]) = max_set := by
          apply le_antisymm
          · apply Finset.le_max'
            simp only [Multiset.mem_toFinset]
            have := @List.getElem_mem _ set.sort n (by simp[h₁])
            rw[Multiset.mem_sort] at this
            exact this
          · apply Finset.max'_le
            simp only [Multiset.mem_toFinset]
            intro x hx
            obtain ⟨i, hi₁, hi₂⟩ :=
              List.getElem_of_mem (show x ∈ set.sort by simp[hx])
            rw[← hi₂]
            obtain h | h | h := lt_trichotomy i n
            · have h' := List.pairwise_iff_getElem.mp
                (set.pairwise_sort (fun a b ↦ decide (a ≤ b)))
                i
                n
                hi₁
                (by simp[h₁])
                h
              simp only [decide_eq_true_eq] at h'
              exact h'
            · simp[h]
            · simp[h₁] at hi₁
              omega
        have sort_sublist : set.sort.Sublist superset.sort := by
          rw
            [ ← Multiset.coe_toList set
            , ← Multiset.coe_toList superset
            , Multiset.coe_sort
            , Multiset.coe_sort
            ]
          apply @List.sublist_of_subperm_of_pairwise
            _ (fun a b ↦ decide <| a ≤ b) _ _
          · trans set.toList
            · apply List.Perm.subperm
              apply List.mergeSort_perm
            trans superset.toList
            · rw[← Multiset.coe_le]
              simp only [Multiset.coe_toList]
              exact h₂
            · apply List.Perm.subperm
              symm
              apply List.mergeSort_perm
          · apply List.pairwise_mergeSort
            · simp only [decide_eq_true_eq]
              exact @le_trans t _
            · simp only [Bool.or_eq_true, decide_eq_true_eq]
              exact LinearOrder.le_total
          · apply List.pairwise_mergeSort
            · simp only [decide_eq_true_eq]
              exact @le_trans t _
            · simp only [Bool.or_eq_true, decide_eq_true_eq]
              exact LinearOrder.le_total
        have : ∃ i : Fin superset.card, n ≤ i ∧ superset.sort[i] = max_set := by
          obtain ⟨is, h₃, h₄⟩ := List.sublist_eq_map_getElem sort_sublist
          have is_len : is.length = n+1 := by
            trans set.sort.length
            · rw[h₃]
              simp
            · simp[h₁]
          refine ⟨Fin.cast (by simp) (is[n]'(by simp[is_len])), ?_, ?_⟩
          · have : ∀ j : Fin is.length, j.val ≤ is[j].val := by
              intro ⟨j, hj⟩
              induction j
              · simp
              · rename_i k hk
                have hk := hk (by omega)
                simp
                have := List.pairwise_iff_getElem.mp
                  h₄
                  k
                  (k + 1)
                  (by omega)
                  hj
                  (by simp)
                simp at hk
                omega
            have := this ⟨n, by simp[is_len]⟩
            simp at this
            simp[this]
          · rw[← max_last_sorted]
            trans
              (is.map (fun x ↦ superset.sort[x]'(x.prop)))[n]'(by simp[is_len])
            · simp
            · congr
              symm
              exact h₃
        obtain ⟨i, hi₁, hi₂⟩ := this
        rw[← hi₂]
        obtain hi₁ | hi₁ := lt_or_eq_of_le hi₁
        · exact List.pairwise_iff_getElem.mp
            (superset.pairwise_sort LE.le)
            n
            i
            (by
              apply Nat.lt_of_succ_le
              simp only [Nat.succ_eq_add_one, ← h₁, Multiset.length_sort]
              exact Multiset.card_le_card h₂
            )
            (by simp[i.prop])
            hi₁
        · simp[hi₁]
  exact fun set superset ↦ this (set.card) set superset (by rfl)

lemma subset_eq_take_min_of_sum_eq {t : Type} [LinearOrder t]
  [AddCancelCommMonoid t] [IsOrderedAddMonoid t] :
    ∀ (set superset : Multiset t) (_ : set ≤ superset),
      (take_min set.card superset).sum = set.sum →
        set = take_min set.card superset := by
  have : ∀ n : ℕ, ∀ (set superset : Multiset t) (_ : set.card = n)
    (_ : set ≤ superset), (take_min set.card superset).sum = set.sum →
      set = take_min set.card superset := fun n ↦ by
    induction n with
    | zero =>
      intro set superset h₁ h₂ h₃
      simp at h₁
      unfold take_min
      simp[h₁]
    | succ n ih =>
      intro set superset set_card set_le_superset set_sum
      have superset_card : n + 1 ≤ superset.card := by
        rw[← set_card]
        exact Multiset.card_le_card set_le_superset
      have set_finset_nonempty : set.toFinset.Nonempty := by
        simp
        intro h
        simp[h] at set_card
      -- idk if this is the best choice of element
      let min_set : t := set.toFinset.min' set_finset_nonempty
      have min_in_set : min_set ∈ set := by
        unfold min_set
        rw[← Multiset.mem_toFinset]
        simp[Finset.min'_mem]
      have min_in_superset : min_set ∈ superset :=
        Multiset.mem_of_le set_le_superset min_in_set
      let small_set : Multiset t := set.erase min_set
      have small_set_card : small_set.card = n := by
        rw[show n = set.card.pred by simp[set_card]]
        exact Multiset.card_erase_of_mem min_in_set
      let small_superset : Multiset t := superset.erase min_set
      have small_superset_card : n ≤ small_superset.card := by
        rw[Multiset.card_erase_of_mem min_in_superset]
        simp
        omega
      have := ih
        small_set
        small_superset
        small_set_card
        (Multiset.erase_le_erase _ set_le_superset)
        (by
          have : set.sum = min_set + small_set.sum := by
            unfold small_set
            rw[← Multiset.cons_erase min_in_set]
            simp
          apply IsLeftCancelAdd.add_left_cancel min_set
          simp only []
          rw[← this, ← set_sum, set_card, small_set_card]
          have := sum_min_superset_le_sum
            (take_min n small_superset)
            superset
            (Trans.trans take_min_le (superset.erase_le min_set))
          simp[take_min_card small_superset_card] at this
          -- idk this seems hard to prove
          have := sum_min_superset_le_sum
            small_set
            small_superset
            (Multiset.erase_le_erase _ set_le_superset)
          have := sum_min_superset_le_sum
            set
            superset
            set_le_superset

        )


lemma bl_cage_digits :
  {digit ⟨0, 7⟩, digit ⟨0, 8⟩} = ({2, 3} : Finset Digit) ∧
  {digit ⟨1, 7⟩, digit ⟨1, 8⟩} = ({1, 9} : Finset Digit) := by
    let cage_cells : Finset Cell := {⟨0, 7⟩, ⟨0, 8⟩, ⟨1, 7⟩, ⟨1, 8⟩}
    let cage : KillerCage := ⟨cage_cells, some (-3)⟩
    let neg_cell := cage_neg ⟨cage, by decide⟩
    let pos_cells := cage_cells.erase neg_cell
    have sum := cage_total_pos_minus_neg ⟨cage, by decide⟩
    unfold cage at sum
    simp at sum
    change pos_cells.sum int_digit - int_digit neg_cell = -3 at sum
    sorry
