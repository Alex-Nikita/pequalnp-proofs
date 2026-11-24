import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1598_aux

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

def vals (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def sets (n : Nat) (gs : List Gate) : List (List Nat) :=
  gs.foldl (orStep n) []

theorem vals_length (gs : List Gate) (x : List Bool) :
    (vals gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [vals]
  | cons g gs ih =>
    simpa [vals, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])

theorem vals_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    vals (gs ++ [g]) x = vals gs x ++
      [g.op.eval (g.inputs.map fun i => (vals gs x).getD i false)] := by
  simp [vals, List.foldl_append]

theorem sets_length (n : Nat) (gs : List Gate) : (sets n gs).length = gs.length := by
  have hf : ∀ (ts : List Gate) (cs : List (List Nat)),
      (ts.foldl (orStep n) cs).length = cs.length + ts.length := by
    intro ts
    induction ts with
    | nil => intro cs; simp
    | cons g ts ih =>
      intro cs
      simpa [List.foldl_cons, orStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (orStep n cs g)
  simpa [sets] using hf gs []

theorem sets_snoc (n : Nat) (gs : List Gate) (g : Gate) :
    sets n (gs ++ [g]) = orStep n (sets n gs) g := by
  simp [sets, List.foldl_append]

theorem vals_old (gs : List Gate) (g : Gate) (x : List Bool) (w : Nat)
    (hw : w < x.length + gs.length) :
    (vals (gs ++ [g]) x).getD w false = (vals gs x).getD w false := by
  rw [vals_snoc, List.getD_append]
  simpa [vals_length] using hw

theorem sets_old (n : Nat) (gs : List Gate) (g : Gate) (j : Nat)
    (hj : j < gs.length) :
    (sets n (gs ++ [g])).getD j [] = (sets n gs).getD j [] := by
  rw [sets_snoc]
  unfold orStep
  rw [List.getD_append]
  simpa [sets_length] using hj

theorem true_index (gs : List Gate) (x : List Bool) (w : Nat)
    (h : (vals gs x).getD w false = true) : w < x.length + gs.length := by
  by_contra hn
  rw [List.getD_eq_default] at h
  · cases h
  · simpa [vals_length] using Nat.le_of_not_gt hn

theorem trace (n : Nat) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (U : Finset (Fin n)) (w : Nat)
    (ht : (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD w false = true)
    (hb : ∀ j < gs.length, n ≤ w → j ∈ (sets n gs).getD (w-n) [] →
      (gs.getD j {op := GateOp.or, inputs := []}).op = GateOp.and →
      (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD (n+j) false = false) :
    ∃ i ∈ U, (vals gs (List.ofFn fun k : Fin n => decide (k = i))).getD w false = true := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    have hw : w < n := by simpa using true_index [] _ w ht
    refine ⟨⟨w, hw⟩, ?_, ?_⟩
    · simpa [vals, hw] using ht
    · simp [vals, hw]
  | @append_singleton gs g ih =>
    have hold : ∀ a ∈ gs, a.op = GateOp.and ∨ a.op = GateOp.or :=
      fun a ha => hops a (List.mem_append_left _ ha)
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := hops g (by simp)
    have hw : w < n + (gs ++ [g]).length := by
      simpa using true_index (gs ++ [g]) _ w ht
    by_cases hwo : w < n + gs.length
    · have hto : (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD w false = true := by
        rw [vals_old] at ht
        · exact ht
        · simpa using hwo
      have hbo : ∀ j < gs.length, n ≤ w → j ∈ (sets n gs).getD (w-n) [] →
          (gs.getD j {op := GateOp.or, inputs := []}).op = GateOp.and →
          (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD (n+j) false = false := by
        intro j hj hn hjc hjop
        have hm : j ∈ (sets n (gs ++ [g])).getD (w-n) [] := by
          rw [sets_old _ _ _ _ (by omega)]
          exact hjc
        have ho : ((gs ++ [g]).getD j {op := GateOp.or, inputs := []}).op = GateOp.and := by
          rwa [List.getD_append _ _ _ _ hj]
        have hz := hb j (by simp; omega) hn hm ho
        rw [vals_old] at hz
        · exact hz
        · simp; omega
      obtain ⟨i, hi, hv⟩ := ih hold w hto hbo
      refine ⟨i, hi, ?_⟩
      rw [vals_old]
      · exact hv
      · simpa using hwo
    · have hwlast : w = n + gs.length := by simp only [List.length_append, List.length_singleton] at hw; omega
      subst w
      have hself : gs.length ∈ (sets n (gs ++ [g])).getD (n + gs.length - n) [] := by
        simp [sets_snoc, orStep, sets_length]
      rcases hop with ha | ho
      · have hoplast : ((gs ++ [g]).getD gs.length {op := GateOp.or, inputs := []}).op = GateOp.and := by
          simpa using ha
        have hf := hb gs.length (by simp) (by omega) hself hoplast
        rw [ht] at hf
        cases hf
      · have hg : g.op.eval (g.inputs.map fun i =>
          (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD i false) = true := by
          simpa [vals_snoc, vals_length] using ht
        obtain ⟨v, hvg, hvt⟩ : ∃ v ∈ g.inputs,
            (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD v false = true := by
          simpa [ho, GateOp.eval] using hg
        have hvbound : v < n + gs.length := by simpa using true_index gs _ v hvt
        have hbchild : ∀ j < gs.length, n ≤ v → j ∈ (sets n gs).getD (v-n) [] →
            (gs.getD j {op := GateOp.or, inputs := []}).op = GateOp.and →
            (vals gs (List.ofFn fun k : Fin n => decide (k ∈ U))).getD (n+j) false = false := by
          intro j hj hnv hjc hjop
          have hm : j ∈ (sets n (gs ++ [g])).getD (n + gs.length - n) [] := by
            simp only [Nat.add_sub_cancel_left, sets_snoc, orStep, sets_length, ho, ite_true]
            rw [show gs.length = (sets n gs).length from (sets_length n gs).symm]
            simp only [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero, List.mem_cons]
            right
            apply List.mem_flatMap.mpr
            refine ⟨v, ?_, hjc⟩
            simp [hvg, hnv, hvbound, sets_length]
          have hjop' : ((gs ++ [g]).getD j {op := GateOp.or, inputs := []}).op = GateOp.and := by
            rwa [List.getD_append _ _ _ _ hj]
          have hz := hb j (by simp; omega) (by omega) hm hjop'
          rw [vals_old] at hz
          · exact hz
          · simp; omega
        obtain ⟨i, hi, hvi⟩ := ih hold v hvt hbchild
        refine ⟨i, hi, ?_⟩
        have hg' : g.op.eval (g.inputs.map fun w =>
            (vals gs (List.ofFn fun k : Fin n => decide (k = i))).getD w false) = true := by
          simp only [ho, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
          exact ⟨v, hvg, hvi⟩
        simpa [vals_snoc, vals_length] using hg'

end PEqualNP.Outside.L_meta_1598_aux

theorem PEqualNP.Outside.L_meta_1598 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → ∀ (U : Finset (Fin n)) (w : ℕ), PEqualNP.CleanedNonEdge.wireVal n C w (fun k : Fin n => decide (k ∈ U)) = true → (∀ g : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal n C g (fun l : Fin n => decide (l ∈ U)) = false) → ∃ i ∈ U, PEqualNP.CleanedNonEdge.wireVal n C w (fun r : Fin n => decide (r = i)) = true := by
  intro n C hc U w ht hb
  apply PEqualNP.Outside.L_meta_1598_aux.trace n C.gates hc U w ht
  intro j hj hn hr hop
  exact hb j ⟨hn, hr⟩ hop
