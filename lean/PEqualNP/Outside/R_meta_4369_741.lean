import PEqualNP.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The finite pattern classes are adapted from billylubanski's checked L-meta-122 (PR 2023).
-- The circuit potential argument excludes four or more NOT gates inside this proof.
-- The remaining cases use the classified pairs of initial wires.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4369_741
    (zeroNot :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (C : Circuit) (R : Finset Nat),
        let u := C.output :: C.gates.flatMap Gate.inputs
        let n := (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length
        FanInTwo C → C.size = 14 → n = 0 → R.card + n ≤ 4 →
        9 + n + ∑ i ∈ Finset.range 24, (u.count i - 1) ≤ 14 → 2 ≤ u.count 9 →
        (∀ g ∈ C.gates, ∀ a b : Fin 10, g.inputs = [a.val,b.val] →
          g.op = .and ∨ g.op = .or → a.val ∉ R → b.val ∉ R →
          10*a.val+b.val ∈ (if g.op.eval [] then [9,39,49,90,93,94,99] else [99] : List Nat)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    (oneNot :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (C : Circuit) (R : Finset Nat),
        let u := C.output :: C.gates.flatMap Gate.inputs
        let n := (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length
        FanInTwo C → C.size = 14 → n = 1 → R.card + n ≤ 4 →
        9 + n + ∑ i ∈ Finset.range 24, (u.count i - 1) ≤ 14 → 2 ≤ u.count 9 →
        (∀ g ∈ C.gates, ∀ a b : Fin 10, g.inputs = [a.val,b.val] →
          g.op = .and ∨ g.op = .or → a.val ∉ R → b.val ∉ R →
          10*a.val+b.val ∈ (if g.op.eval [] then [9,39,49,90,93,94,99] else [99] : List Nat)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    (twoThreeNot :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (C : Circuit) (R : Finset Nat),
        let u := C.output :: C.gates.flatMap Gate.inputs
        let n := (C.gates.filter (fun g => g.op.eval [false] && !g.op.eval [true])).length
        FanInTwo C → C.size = 14 → 2 ≤ n → n ≤ 3 → R.card + n ≤ 4 →
        9 + n + ∑ i ∈ Finset.range 24, (u.count i - 1) ≤ 14 → 2 ≤ u.count 9 →
        (∀ g ∈ C.gates, ∀ a b : Fin 10, g.inputs = [a.val,b.val] →
          g.op = .and ∨ g.op = .or → a.val ∉ R → b.val ∉ R →
          10*a.val+b.val ∈ (if g.op.eval [] then [9,39,49,90,93,94,99] else [99] : List Nat)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) ≠ f x)
    :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.GateOp → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.GateOp) => if x3.eval [] = Bool.true then [(3 : ℕ), (9 : ℕ), (30 : ℕ), (39 : ℕ), (49 : ℕ)] else [(2 : ℕ), (4 : ℕ), (8 : ℕ), (31 : ℕ), (34 : ℕ), (35 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : List ℕ := x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;   have x6 : ℕ := (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false] && !x6.op.eval [Bool.true]) x4.gates).length;   PEqualNP.MetaComplexity.FanInTwo x4 → x4.size = (14 : ℕ) → (∀ x9 ∈ x5, x9 ≤ (24 : ℕ)) → (∀ x10 < (24 : ℕ), x10 ∈ x5) → (9 : ℕ) + x6 + ∑ x11 ∈ Finset.range (24 : ℕ), (List.count x11 x5 - (1 : ℕ)) ≤ (14 : ℕ) → (2 : ℕ) ≤ List.count (9 : ℕ) x5 → (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x14 ++ [x14 x13]) ≠ x1 x14) → ∀ (x14 : Finset ℕ), x14.card + x6 ≤ (4 : ℕ) → (∀ x16 ∈ x4.gates, ∀ (x18 : Fin (9 : ℕ)) (x19 : Fin (10 : ℕ)), x16.inputs = [↑x18, ↑x19] ∨ x16.inputs = [↑x19, ↑x18] → x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) * ↑x18 + ↑x19 ∉ x3 x16.op → ↑x18 ∈ x14) → ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates ∨ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(3 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates → (0 : ℕ) ∈ x14 ∨ (3 : ℕ) ∈ x14) → ∃ (x18 : Fin (9 : ℕ) → Bool), x4.eval (x2 x18) ≠ x1 x18 := by
  classical
  have eval_and (xs : List Bool) : GateOp.and.eval xs = xs.all id := by rfl
  have eval_or (xs : List Bool) : GateOp.or.eval xs = xs.any id := by rfl
  have eval_not (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := by rfl
  have wires_def (C : Circuit) (xs : List Bool) : C.wires xs =
      C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs := by rfl

  let allowed (k : ℕ) : List (BitVec 8) :=
    if k = 0 then [0, 15, 240, 255]
    else if k = 1 then [0, 3, 5, 10, 12, 15, 48, 51, 63, 80, 85, 95, 160, 170, 175, 192, 204, 207, 240, 243, 245, 250, 252, 255]
    else [0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 19, 21, 31, 32, 34, 35, 42, 47, 48, 49, 50, 51, 53, 55, 58, 59, 60, 63, 64, 68, 69, 76, 79, 80, 81, 83, 84, 85, 87, 90, 92, 93, 95, 112, 115, 117, 119, 127, 128, 136, 138, 140, 143, 160, 162, 163, 165, 168, 170, 171, 172, 174, 175, 176, 179, 186, 187, 191, 192, 195, 196, 197, 200, 202, 204, 205, 206, 207, 208, 213, 220, 221, 223, 224, 234, 236, 238, 239, 240, 241, 242, 243, 244, 245, 247, 248, 250, 251, 252, 253, 254, 255]

  let combines (i j : ℕ) : Bool :=
    (allowed i).all fun x => (allowed j).all fun y =>
      (allowed (i+j)).contains (x &&& y) && (allowed (i+j)).contains (x ||| y)

  have closure : ∀ i j : Fin 3, i.val+j.val ≤ 2 → combines i j = true := by
    dsimp only [combines, allowed]
    decide

  -- Certificate closure ends here.
  have combine {i j : ℕ} (h : i+j ≤ 2) (x y : BitVec 8)
      (hx : x ∈ allowed i) (hy : y ∈ allowed j) :
      (x &&& y) ∈ allowed (i+j) ∧ (x ||| y) ∈ allowed (i+j) := by
    have hc := closure ⟨i, by omega⟩ ⟨j, by omega⟩ h
    change (allowed i).all _ = true at hc
    have hxy := List.all_eq_true.mp (List.all_eq_true.mp hc x hx) y hy
    simpa using hxy

  let cost (x : BitVec 8) : Nat :=
    if x ∈ allowed 0 then 0 else if x ∈ allowed 1 then 1 else if x ∈ allowed 2 then 2 else 3

  have cost_le_three (x : BitVec 8) : cost x ≤ 3 := by
    unfold cost
    split <;> (try split) <;> (try split) <;> omega

  have nesting01 : (allowed 0).all (fun x => (allowed 1).contains x) = true := by
    dsimp only [allowed]
    decide
  have nesting12 : (allowed 1).all (fun x => (allowed 2).contains x) = true := by
    dsimp only [allowed]
    decide

  have subset01 {x : BitVec 8} (h : x ∈ allowed 0) : x ∈ allowed 1 :=
    List.contains_iff_mem.mp (List.all_eq_true.mp nesting01 x h)

  have subset12 {x : BitVec 8} (h : x ∈ allowed 1) : x ∈ allowed 2 :=
    List.contains_iff_mem.mp (List.all_eq_true.mp nesting12 x h)

  have cost_mem : ∀ (k : Fin 3) (x : BitVec 8), cost x ≤ k.val ↔ x ∈ allowed k.val := by
    intro k x
    by_cases h0 : x ∈ allowed 0
    · have h1 := subset01 h0
      have h2 := subset12 h1
      fin_cases k <;> simp [cost,h0,h1,h2]
    · by_cases h1 : x ∈ allowed 1
      · have h2 := subset12 h1
        fin_cases k <;> simp [cost,h0,h1,h2]
      · by_cases h2 : x ∈ allowed 2
        · fin_cases k <;> simp [cost,h0,h1,h2]
        · fin_cases k <;> simp [cost,h0,h1,h2]

  have complement_closed : ∀ k : Fin 3,
      (allowed k.val).all (fun x => (allowed k.val).contains (~~~x)) = true := by
    dsimp only [allowed]
    decide

  have cost_and (x y : BitVec 8) : cost (x &&& y) ≤ cost x + cost y := by
    by_cases h : cost x + cost y ≤ 2
    · apply (cost_mem ⟨cost x + cost y, by omega⟩ _).mpr
      exact (combine h x y ((cost_mem ⟨cost x, by omega⟩ x).mp le_rfl)
        ((cost_mem ⟨cost y, by omega⟩ y).mp le_rfl)).1
    · have := cost_le_three (x &&& y)
      omega

  have cost_or (x y : BitVec 8) : cost (x ||| y) ≤ cost x + cost y := by
    by_cases h : cost x + cost y ≤ 2
    · apply (cost_mem ⟨cost x + cost y, by omega⟩ _).mpr
      exact (combine h x y ((cost_mem ⟨cost x, by omega⟩ x).mp le_rfl)
        ((cost_mem ⟨cost y, by omega⟩ y).mp le_rfl)).2
    · have := cost_le_three (x ||| y)
      omega

  have cost_not (x : BitVec 8) : cost (~~~x) ≤ cost x := by
    by_cases h : cost x ≤ 2
    · apply (cost_mem ⟨cost x, by omega⟩ _).mpr
      have hx := (cost_mem ⟨cost x, by omega⟩ x).mp le_rfl
      have hc := List.all_eq_true.mp (complement_closed ⟨cost x, by omega⟩) x hx
      exact List.contains_iff_mem.mp hc
    · have := cost_le_three (~~~x)
      omega

  have cost_zero : cost 0 = 0 := by
    dsimp only [cost, allowed]
    decide
  have cost_ones : cost 255 = 0 := by
    dsimp only [cost, allowed]
    decide
  have cost_target : cost 232 = 3 := by
    dsimp only [cost, allowed]
    decide

  let run {α : Type} (ev : GateOp → List α → α) (zero : α)
      (gs : List Gate) (seed : List α) : List α :=
    gs.foldl (fun w g => w ++ [ev g.op (g.inputs.map fun i => w.getD i zero)]) seed

  have run_extends {α : Type} (ev : GateOp → List α → α) (zero : α)
      (gs : List Gate) (seed : List α) : ∃ tail, run ev zero gs seed = seed ++ tail := by
    induction gs generalizing seed with
    | nil => exact ⟨[], by simp [run]⟩
    | cons g gs ih =>
      obtain ⟨tail, h⟩ := ih (seed ++ [ev g.op (g.inputs.map fun i => seed.getD i zero)])
      exact ⟨_ :: tail, by simpa [run, List.foldl_cons, List.append_assoc] using h⟩

  have cost_prefix {α : Type} (ev : GateOp → List α → α) (zero : α)
      (c : α → Nat) (hz : c zero = 0) (gs : List Gate) (seed : List α) (i : Nat) :
      c (seed.getD i zero) ≤ c ((run ev zero gs seed).getD i zero) := by
    obtain ⟨tail, ht⟩ := run_extends ev zero gs seed
    rw [ht]
    by_cases hi : i < seed.length
    · rw [List.getD_append _ _ _ _ hi]
    · rw [List.getD_eq_default seed zero (by omega), hz]
      omega

  have sum_map_mono (xs : List Nat) (f g : Nat → Nat) (h : ∀ i ∈ xs, f i ≤ g i) :
      (xs.map f).sum ≤ (xs.map g).sum := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have ha := h a (by simp)
      have ht := ih (fun i hi => h i (by simp [hi]))
      omega

  have run_cost_bound {α : Type} (ev : GateOp → List α → α) (zero : α)
      (c : α → Nat) (hz : c zero = 0) (gs : List Gate)
      (hc : ∀ g ∈ gs, ∀ w : List α, c (ev g.op w) ≤ (w.map c).sum)
      (seed : List α) :
      ((run ev zero gs seed).map c).sum ≤ (seed.map c).sum +
        ((gs.flatMap Gate.inputs).map fun i => c ((run ev zero gs seed).getD i zero)).sum := by
    induction gs generalizing seed with
    | nil => simp [run]
    | cons g gs ih =>
      let v := ev g.op (g.inputs.map fun i => seed.getD i zero)
      let all := run ev zero gs (seed ++ [v])
      have hsub := ih (fun g' hg' => hc g' (by simp [hg'])) (seed ++ [v])
      have hv : c v ≤ (g.inputs.map fun i => c (all.getD i zero)).sum := by
        have he := hc g (by simp) (g.inputs.map fun i => seed.getD i zero)
        simp only [List.map_map, Function.comp_def] at he
        apply he.trans
        apply sum_map_mono
        intro i hi
        exact cost_prefix ev zero c hz (g :: gs) seed i
      change (all.map c).sum ≤ _ at hsub ⊢
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero] at hsub
      change (all.map c).sum ≤ (seed.map c).sum + c v +
        ((gs.flatMap Gate.inputs).map fun i => c (all.getD i zero)).sum at hsub
      change (all.map c).sum ≤ (seed.map c).sum +
        ((g.inputs ++ gs.flatMap Gate.inputs).map fun i => c (all.getD i zero)).sum
      simp only [List.map_append, List.sum_append]
      omega

  have counted_sum (u : List Nat) (w : Nat → Nat) (N : Nat)
      (outside : ∀ i, N ≤ i → w i = 0) :
      (u.map w).sum = ∑ i ∈ Finset.range N, u.count i * w i := by
    rw [Finset.sum_list_map_count]
    simp only [nsmul_eq_mul]
    apply Finset.sum_congr_of_eq_on_inter
    · intro i hi hnot
      have hout : N ≤ i := by simpa using hnot
      simp [outside i hout]
    · intro i hi hnot
      have hcount : u.count i = 0 := List.count_eq_zero.mpr (by simpa using hnot)
      simp [hcount]
    · intro i hi hboth
      rfl

  have refs_bound {α : Type} (zero : α) (c : α → Nat) (hz : c zero = 0)
      (all : List α) (u : List Nat) (exception : Nat)
      (hzero : c (all.getD exception zero) = 0)
      (hcount : ∀ i < all.length, i ≠ exception → u.count i ≤ 1) :
      (u.map fun i => c (all.getD i zero)).sum ≤ (all.map c).sum := by
    rw [counted_sum u (fun i => c (all.getD i zero)) all.length (by
      intro i hi
      rw [List.getD_eq_default all zero hi, hz])]
    have eqsum : ∀ xs : List α, (xs.map c).sum = ∑ i ∈ Finset.range xs.length, c (xs.getD i zero) := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simpa [Finset.sum_range_succ', Nat.add_comm] using congrArg (fun z => c a + z) ih
    rw [eqsum all]
    apply Finset.sum_le_sum
    intro i hi
    by_cases he : i = exception
    · subst i
      rw [hzero]
      simp
    · have hc := hcount i (Finset.mem_range.mp hi) he
      nlinarith

  have output_bound {α : Type} (ev : GateOp → List α → α) (zero : α)
      (c : α → Nat) (hz : c zero = 0) (gs : List Gate) (out : Nat)
      (hc : ∀ g ∈ gs, ∀ w : List α, c (ev g.op w) ≤ (w.map c).sum)
      (seed : List α) (exception : Nat)
      (hzero : c ((run ev zero gs seed).getD exception zero) = 0)
      (hcount : ∀ i < (run ev zero gs seed).length, i ≠ exception →
        (out :: gs.flatMap Gate.inputs).count i ≤ 1) :
      c ((run ev zero gs seed).getD out zero) ≤ (seed.map c).sum := by
    have hrun := run_cost_bound ev zero c hz gs hc seed
    have href := refs_bound zero c hz (run ev zero gs seed) (out :: gs.flatMap Gate.inputs)
      exception hzero hcount
    simp only [List.map_cons, List.sum_cons] at href
    omega

  have budget_forces_linear (u : List Nat) (z : Nat) (hz : 4 ≤ z)
      (h9 : 2 ≤ u.count 9)
      (budget : 9 + z + ∑ i ∈ Finset.range 24, (u.count i - 1) ≤ 14) :
      ∀ i < 24, i ≠ 9 → u.count i ≤ 1 := by
    intro i hi hne
    have sub : ({i,9} : Finset Nat) ⊆ Finset.range 24 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact Finset.mem_range.mpr hi
      · decide
    have bound := Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => u.count j - 1)
      sub (by intros; omega)
    simp [hne] at bound
    omega

  let ev (op : GateOp) (xs : List (BitVec 8)) : BitVec 8 :=
    if op.eval [] then
      if op.eval [true] then xs.foldr (· &&& ·) 255 else ~~~(xs.headD 0)
    else xs.foldr (· ||| ·) 0

  have ev_cost (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
      (xs : List (BitVec 8)) : cost (ev op xs) ≤ (xs.map cost).sum := by
    rcases hop with rfl | rfl | rfl
    · induction xs with
      | nil =>
        change cost (255 : BitVec 8) ≤ 0
        rw [cost_ones]
      | cons x xs ih =>
        exact (cost_and _ _).trans (Nat.add_le_add_left ih _)
    · induction xs with
      | nil =>
        change cost (0 : BitVec 8) ≤ 0
        rw [cost_zero]
      | cons x xs ih =>
        exact (cost_or _ _).trans (Nat.add_le_add_left ih _)
    · cases xs with
      | nil =>
        change cost (255 : BitVec 8) ≤ 0
        rw [cost_ones]
      | cons x xs =>
        change cost (~~~x) ≤ cost x + _
        exact (cost_not x).trans (Nat.le_add_right _ _)

  have ev_bits (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not)
      (xs : List (BitVec 8)) (i : Nat) (hi : i < 8) :
      (ev op xs).getLsbD i = op.eval (xs.map fun x => x.getLsbD i) := by
    rcases hop with rfl | rfl | rfl
    · induction xs with
      | nil =>
        change (BitVec.allOnes 8).getLsbD i = true
        simpa only [BitVec.getLsbD_allOnes, decide_eq_true_eq] using hi
      | cons x xs ih => simpa [ev, eval_and, eval_or, eval_not] using congrArg (fun b => x.getLsbD i && b) ih
    · induction xs with
      | nil => simp [ev, eval_and, eval_or, eval_not]
      | cons x xs ih => simpa [ev, eval_and, eval_or, eval_not] using congrArg (fun b => x.getLsbD i || b) ih
    · cases xs with
      | nil =>
        change (BitVec.allOnes 8).getLsbD i = true
        simpa only [BitVec.getLsbD_allOnes, decide_eq_true_eq] using hi
      | cons x xs => simp [ev, eval_and, eval_or, eval_not, hi]

  have getD_map_bits (xs : List (BitVec 8)) (w i : Nat) :
      (xs.map fun x => x.getLsbD i).getD w false = (xs.getD w 0).getLsbD i := by
    induction xs generalizing w with
    | nil => simp
    | cons x xs ih => cases w <;> simp_all

  have run_bits (gs : List Gate)
      (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
      (seed : List (BitVec 8)) (i : Nat) (hi : i < 8) :
      (run ev 0 gs seed).map (fun x => x.getLsbD i) =
        (Circuit.wires ⟨gs,0⟩ (seed.map fun x => x.getLsbD i)) := by
    induction gs generalizing seed with
    | nil => rfl
    | cons g gs ih =>
      change (run ev 0 gs (seed ++ [ev g.op (g.inputs.map fun w => seed.getD w 0)])).map _ = _
      rw [ih (fun a ha => hops a (by simp [ha]))]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [ev_bits g.op (hops g (by simp)) _ i hi]
      simp only [List.map_map, Function.comp_def]
      simp only [wires_def, List.foldl_cons]
      congr 2
      congr 1
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro j hj
      exact (getD_map_bits seed j i).symm

  have run_length (gs : List Gate) (seed : List (BitVec 8)) :
      (run ev 0 gs seed).length = seed.length + gs.length := by
    induction gs generalizing seed with
    | nil => simp [run]
    | cons g gs ih =>
      change (run ev 0 gs (seed ++ [_])).length = _
      rw [ih]
      simp
      omega

  let seed : List (BitVec 8) := [0,170,204,0,0,0,240,240,0,0]

  let input (i : Nat) : Fin 9 → Bool := fun j => (seed.getD j.val 0).getLsbD i

  let f9 (x : Fin 9 → Bool) : Bool :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any fun e =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

  have seed_bits (i : Nat) : seed.map (fun x => x.getLsbD i) =
      List.ofFn (input i) ++ [input i 0 || input i 3] := by
    simp [seed, input, List.ofFn_succ]

  have seed_cost : (seed.map cost).sum = 2 := by
    dsimp only [seed, cost, allowed]
    decide +kernel

  have f9_bits : ∀ i : Fin 8, f9 (input i.val) = (232 : BitVec 8).getLsbD i.val := by
    dsimp only [f9, input, seed]
    decide +kernel

  have not_four (C : Circuit) (fan : FanInTwo C) (size : C.size = 14)
      (h9 : 2 ≤ (C.output :: C.gates.flatMap Gate.inputs).count 9)
      (neg : 4 ≤ (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length)
      (budget : 9 + (C.gates.filter fun g => g.op.eval [false] && !g.op.eval [true]).length +
        ∑ i ∈ Finset.range 24, ((C.output :: C.gates.flatMap Gate.inputs).count i - 1) ≤ 14)
      (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 3]) = f9 x) : False := by
    let all := run ev 0 C.gates seed
    have hops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      intro g hg
      simpa using (fan g hg).1
    have hlen : all.length = 24 := by
      rw [run_length]
      change 10 + C.size = 24
      omega
    have hzero : cost (all.getD 9 0) = 0 := by
      obtain ⟨tail, ht⟩ := run_extends ev (0 : BitVec 8) C.gates seed
      change cost ((run ev 0 C.gates seed).getD 9 0) = 0
      rw [ht, List.getD_append _ _ _ _ (by decide)]
      exact cost_zero
    have upper := output_bound ev (0 : BitVec 8) cost cost_zero C.gates C.output
      (fun g hg w => ev_cost g.op (hops g hg) w) seed 9 hzero (by
        rw [hlen]
        exact budget_forces_linear _ _ neg h9 budget)
    rw [seed_cost] at upper
    have target : all.getD C.output 0 = (232 : BitVec 8) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [← getD_map_bits all C.output i]
      change ((run ev 0 C.gates seed).map (fun x => x.getLsbD i)).getD C.output false = _
      rw [run_bits C.gates hops seed i hi, seed_bits]
      change C.eval (List.ofFn (input i) ++ [input i 0 || input i 3]) = _
      rw [computes]
      exact f9_bits ⟨i,hi⟩
    change cost (all.getD C.output 0) ≤ 2 at upper
    rw [target, cost_target] at upper
    omega

  let exceptions (op : GateOp) : List Nat :=
    if op.eval [] then [3,9,30,39,49] else [2,4,8,31,34,35]

  have finite_classification : ∀ (isAnd : Bool) (a b : Fin 10),
      (a.val < 9 → 10*a.val+b.val ∈
        (if isAnd then [3,9,30,39,49] else [2,4,8,31,34,35] : List Nat)) →
      (b.val < 9 → 10*b.val+a.val ∈
        (if isAnd then [3,9,30,39,49] else [2,4,8,31,34,35] : List Nat)) →
      (isAnd = true → ¬ ((a.val = 0 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 0))) →
      (a.val = 9 ∧ b.val = 9) ∨
        (isAnd = true ∧
         ((a.val = 9 ∧ b.val ∈ ([0,3,4] : List Nat)) ∨
          (b.val = 9 ∧ a.val ∈ ([0,3,4] : List Nat)))) := by
    intro isAnd a b
    cases isAnd <;> fin_cases a <;> fin_cases b <;> decide

  have initial_pair_classification
      (C : Circuit) (R : Finset Nat)
      (forcing : ∀ g ∈ C.gates, ∀ (a : Fin 9) (b : Fin 10),
        g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val] →
        g.op = .and ∨ g.op = .or → 10*a.val+b.val ∉ exceptions g.op → a.val ∈ R)
      (special : (⟨.and,[0,3]⟩ : Gate) ∈ C.gates ∨ (⟨.and,[3,0]⟩ : Gate) ∈ C.gates →
        0 ∈ R ∨ 3 ∈ R)
      (g : Gate) (hg : g ∈ C.gates) (a b : Fin 10)
      (inputs : g.inputs = [a.val,b.val]) (op : g.op = .and ∨ g.op = .or)
      (ha : a.val ∉ R) (hb : b.val ∉ R) :
      (a.val = 9 ∧ b.val = 9) ∨
        (g.op = .and ∧
         ((a.val = 9 ∧ b.val ∈ ([0,3,4] : List Nat)) ∨
          (b.val = 9 ∧ a.val ∈ ([0,3,4] : List Nat)))) := by
    have left (h : a.val < 9) : 10*a.val+b.val ∈ exceptions g.op := by
      by_contra hn
      exact ha (forcing g hg ⟨a.val,h⟩ b (Or.inl inputs) op hn)
    have right (h : b.val < 9) : 10*b.val+a.val ∈ exceptions g.op := by
      by_contra hn
      exact hb (forcing g hg ⟨b.val,h⟩ a (Or.inr inputs) op hn)
    have noSpecial (hop : g.op = .and) :
        ¬ ((a.val = 0 ∧ b.val = 3) ∨ (a.val = 3 ∧ b.val = 0)) := by
      rintro (⟨h0,h3⟩ | ⟨h3,h0⟩)
      · have he : g = (⟨.and,[0,3]⟩ : Gate) := by
          cases g
          simp_all
        have h := special (Or.inl (he ▸ hg))
        rcases h with h | h
        · exact ha (h0 ▸ h)
        · exact hb (h3 ▸ h)
      · have he : g = (⟨.and,[3,0]⟩ : Gate) := by
          cases g
          simp_all
        have h := special (Or.inr (he ▸ hg))
        rcases h with h | h
        · exact hb (h0 ▸ h)
        · exact ha (h3 ▸ h)
    rcases op with hop | hop
    · have h := finite_classification true a b
        (by simpa [exceptions,hop,eval_and, eval_or, eval_not] using left)
        (by simpa [exceptions,hop,eval_and, eval_or, eval_not] using right) (fun _ => noSpecial hop)
      simpa only [Bool.true_eq, true_and, hop] using h
    · have h := finite_classification false a b
        (by simpa [exceptions,hop,eval_and, eval_or, eval_not] using left)
        (by simpa [exceptions,hop,eval_and, eval_or, eval_not] using right) (by simp)
      exact Or.inl (by simpa using h)


  have initial_codes (C : Circuit) (R : Finset Nat)
      (forcing : ∀ g ∈ C.gates, ∀ (a : Fin 9) (b : Fin 10),
        g.inputs = [a.val,b.val] ∨ g.inputs = [b.val,a.val] →
        g.op = .and ∨ g.op = .or → 10*a.val+b.val ∉ exceptions g.op → a.val ∈ R)
      (special : (⟨.and,[0,3]⟩ : Gate) ∈ C.gates ∨ (⟨.and,[3,0]⟩ : Gate) ∈ C.gates →
        0 ∈ R ∨ 3 ∈ R)
      (g : Gate) (hg : g ∈ C.gates) (a b : Fin 10)
      (inputs : g.inputs = [a.val,b.val]) (op : g.op = .and ∨ g.op = .or)
      (ha : a.val ∉ R) (hb : b.val ∉ R) :
      10*a.val+b.val ∈ (if g.op.eval [] then [9,39,49,90,93,94,99] else [99] : List Nat) := by
    rcases initial_pair_classification C R forcing special g hg a b inputs op ha hb with same | ⟨hop, rest⟩
    · rcases same with ⟨ha,hb⟩
      rcases op with hop | hop <;> simp [hop, eval_and, eval_or, eval_not, ha, hb]
    · rcases rest with ⟨ha,hb⟩ | ⟨hb,ha⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with hb | hb | hb <;> simp [hop, eval_and, eval_or, eval_not, ha, hb]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with ha | ha | ha <;> simp [hop, eval_and, eval_or, eval_not, ha, hb]

  intro f pins exc C u neg fan size bounded used budget reused copies R rbudget forcing special
  have codes := initial_codes C R forcing special
  by_cases hfour : 4 ≤ neg
  · by_contra! computes
    exact not_four C fan size reused hfour budget computes
  · have nle : neg ≤ 3 := by omega
    by_cases h0 : neg = 0
    · exact zeroNot C R fan size h0 rbudget budget reused codes
    · by_cases h1 : neg = 1
      · exact oneNot C R fan size h1 rbudget budget reused codes
      · exact twoThreeNot C R fan size (by omega) nle rbudget budget reused codes
