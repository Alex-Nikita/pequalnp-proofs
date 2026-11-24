import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2600_2
    (hNormalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit), G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C = graphFun G ∅ →
    ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size)
    (hAccounting : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hResidual : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj],
    G = SimpleGraph.fromRel (fun u v : Fin 26 =>
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + 26 - v.val) % 13 ∈ [0, 1, 3, 9]) →
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (Ustar G C).card →
      (Ustar G C).card + 12 ≤ (tops G C \ centreless G C).card +
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (63 : ℕ) ≤ x1.size := by
  intro C gates computes
  let G : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun u v =>
    u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + 26 - v.val) % 13 ∈ [0, 1, 3, 9]

  letI : DecidableRel G.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromRel _).Adj)

  let p (i : Fin 13) : Fin 26 := Fin.castAdd 13 i
  let l (i : Fin 13) : Fin 26 := Fin.natAdd 13 i

  have edge_count : G.edgeFinset.card = 52 := by decide

  have no_four : NoFourCycle G := by decide

  have match_zero : ∀ i : Fin 13, G.Adj (p i) (l i) := by decide
  have match_one : ∀ i : Fin 13, G.Adj (p (i + 1)) (l i) := by decide

  have separate_matchings : ∀ i j : Fin 13,
      s(p i, l i) ≠ s(p (j + 1), l j) := by decide

  have matching_cover (a b : Fin 13 → Fin 26)
      (ai : Function.Injective a) (bi : Function.Injective b)
      (separate : ∀ i j, a i ≠ b j)
      (K : Finset (Fin 26)) (covered : ∀ i, a i ∈ K ∨ b i ∈ K) : 13 ≤ K.card := by
    classical
    let f : Fin 13 → K := fun i =>
      if h : a i ∈ K then ⟨a i, h⟩ else ⟨b i, (covered i).resolve_left h⟩
    have injective : Function.Injective f := by
      intro i j same
      have val := congrArg Subtype.val same
      by_cases hi : a i ∈ K <;> by_cases hj : a j ∈ K
      · exact ai (by simpa [f, hi, hj] using val)
      · exact False.elim (separate i j (by simpa [f, hi, hj] using val))
      · exact False.elim (separate j i (by simpa [f, hi, hj] using val.symm))
      · exact bi (by simpa [f, hi, hj] using val)
    have bound := Fintype.card_le_of_injective f injective
    simpa using bound

  have cover_after_one (U : Finset (Sym2 (Fin 26))) (small : U.card ≤ 1)
      (K : Finset (Fin 26)) (cover : (G.deleteEdges ↑U).IsVertexCover ↑K) : 13 ≤ K.card := by
    have pair_unique : ∀ a ∈ U, ∀ b ∈ U, a = b := Finset.card_le_one.mp small
    by_cases intact : ∀ i : Fin 13, s(p i, l i) ∉ U
    · apply matching_cover p l (by decide) (by decide) (by decide) K
      intro i
      exact cover (SimpleGraph.deleteEdges_adj.mpr ⟨match_zero i, intact i⟩)
    · push Not at intact
      obtain ⟨i, hit⟩ := intact
      apply matching_cover (fun j => p (j + 1)) l (by decide) (by decide) (by decide) K
      intro j
      apply cover
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨match_one j, ?_⟩
      intro second
      exact separate_matchings i j (pair_unique _ hit _ second)

  have exists_min_cover (H : SimpleGraph (Fin 26)) :
      ∃ K : Finset (Fin 26), IsMinCover H K := by
    classical
    have ex : ∃ k : Nat, ∃ K : Finset (Fin 26), H.IsVertexCover ↑K ∧ K.card = k :=
      ⟨26, Finset.univ, by simp, by simp⟩
    obtain ⟨K, hK, hk⟩ := Nat.find_spec ex
    refine ⟨K, hK, ?_⟩
    intro T hT
    have hmin := Nat.find_min' ex
      (show ∃ K : Finset (Fin 26), H.IsVertexCover ↑K ∧ K.card = T.card from ⟨T,hT,rfl⟩)
    omega

  have cross : ∀ i j : Fin 13, G.Adj (p i) (l j) ↔
      i = j ∨ i = j + 1 ∨ i = j + 3 ∨ i = j + 9 := by decide
  have no_pp : ∀ i j : Fin 13, ¬ G.Adj (p i) (p j) := by decide
  have no_ll : ∀ i j : Fin 13, ¬ G.Adj (l i) (l j) := by decide
  have graph_spec (x : Fin 26 → Bool) :
      (∃ a b : Fin 26, G.Adj a b ∧ x a = true ∧ x b = true) ↔
      ∃ i j : Fin 13, (i = j ∨ i = j + 1 ∨ i = j + 3 ∨ i = j + 9) ∧
        x (p i) = true ∧ x (l j) = true := by
    constructor
    · rintro ⟨a, b, adjacent, ha, hb⟩
      induction a using Fin.addCases (m := 13) (n := 13) with
      | left i =>
        induction b using Fin.addCases (m := 13) (n := 13) with
        | left j => exact (no_pp i j adjacent).elim
        | right j => exact ⟨i, j, (cross i j).mp adjacent, ha, hb⟩
      | right i =>
        induction b using Fin.addCases (m := 13) (n := 13) with
        | left j => exact ⟨j, i, (cross j i).mp adjacent.symm, hb, ha⟩
        | right j => exact (no_ll i j adjacent).elim
    · rintro ⟨i, j, incidence, hi, hj⟩
      exact ⟨p i, l j, (cross i j).mpr incidence, hi, hj⟩
  have monotone : Monotone2 C := by
    intro g member
    obtain ⟨j, atGate⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨op, a, b, inputs, _, _, _⟩ := gates j g atGate
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using op
    · simp [inputs]
  have computesGraph : circuitFun 26 C = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔ graphFun G ∅ x = true
    rw [computes]
    change _ ↔ (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) ||
      decide (∃ a b : Fin 26, G.Adj a b ∧ x a = true ∧ x b = true)) = true
    simpa only [Finset.exists_mem_empty_iff, decide_false,
      Bool.false_or, decide_eq_true_eq, p, l] using (graph_spec x).symm
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D, least, top, small⟩ := hNormalize 26 G C nonempty monotone computesGraph
  obtain ⟨budget, covers⟩ := hAccounting 26 G D no_four nonempty least top
  rw [edge_count] at budget
  by_cases few : (Ustar G D).card ≤ 1
  · obtain ⟨K, minimal⟩ := exists_min_cover (G.deleteEdges ↑(Ustar G D))
    have lower := cover_after_one (Ustar G D) few K minimal.1
    have upper := covers K minimal
    omega
  · have remaining := hResidual G rfl D least top (by omega)
    omega
