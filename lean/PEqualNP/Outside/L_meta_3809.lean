import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3809

open PEqualNP.CircuitLowerBounds

/-- Relabel a wire: the first nine wires go through `f`, every other wire is kept. -/
def relabel (f : Fin 9 → Fin 9) (w : ℕ) : ℕ := if h : w < 9 then (f ⟨w, h⟩ : ℕ) else w

theorem relabel_of_ge (f : Fin 9 → Fin 9) {w : ℕ} (h : 9 ≤ w) : relabel f w = w := by
  simp [relabel, Nat.not_lt.mpr h]

theorem relabel_lt (f : Fin 9 → Fin 9) {w n : ℕ} (hn : 9 ≤ n) (hw : w < n) : relabel f w < n := by
  unfold relabel
  split_ifs with h
  · exact lt_of_lt_of_le (f ⟨w, h⟩).isLt hn
  · exact hw

/-- The gate with its input wires relabelled. -/
def relabelGate (f : Fin 9 → Fin 9) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (relabel f) }

/-- Wire lists in step: same length, at least nine wires, and wire `i` of the original reads
wire `relabel f i` of the relabelled one. -/
def Rel (f : Fin 9 → Fin 9) (w w' : List Bool) : Prop :=
  w.length = w'.length ∧ 9 ≤ w.length ∧ ∀ i, w'.getD i false = w.getD (relabel f i) false

theorem rel_step (f : Fin 9 → Fin 9) (g : Gate) {w w' : List Bool} (h : Rel f w w') :
    Rel f (w ++ [(relabelGate f g).op.eval ((relabelGate f g).inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) := by
  obtain ⟨hlen, h9, hval⟩ := h
  have hv : (relabelGate f g).op.eval ((relabelGate f g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
    simp only [relabelGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact (hval i).symm
  rw [hv]
  refine ⟨by simp [hlen], by simp; omega, ?_⟩
  intro i
  rcases lt_trichotomy i w'.length with hi | hi | hi
  · have hm : relabel f i < w.length := relabel_lt f h9 (by omega)
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hm]
    exact hval i
  · have hge : 9 ≤ i := by omega
    rw [relabel_of_ge f hge, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    simp [hlen, hi]
  · have hge : 9 ≤ i := by omega
    rw [relabel_of_ge f hge, List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (f : Fin 9 → Fin 9) (gs : List Gate) : ∀ (w w' : List Bool), Rel f w w' →
    Rel f ((gs.map (relabelGate f)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w') := by
  induction gs with
  | nil => intro w w' h; simpa using h
  | cons g gs ih =>
    intro w w' h
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (rel_step f g h)

theorem ofFn_getD (g : Fin 9 → Bool) (i : ℕ) (hi : i < 9) : (List.ofFn g).getD i false = g ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem rel_init (f : Fin 9 → Fin 9) (x : Fin 9 → Bool) (a b : Bool) :
    Rel f (List.ofFn x ++ [a, b]) (List.ofFn (x ∘ f) ++ [a, b]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases hi : i < 9
  · have hf : relabel f i = (f ⟨i, hi⟩ : ℕ) := by simp [relabel, hi]
    rw [hf, List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simp)]
    rw [ofFn_getD _ i hi, ofFn_getD _ _ (f ⟨i, hi⟩).isLt]
    rfl
  · have hge : 9 ≤ i := by omega
    rw [relabel_of_ge f hge, List.getD_append_right _ _ _ _ (by simpa using hge),
      List.getD_append_right _ _ _ _ (by simpa using hge)]
    simp

end PEqualNP.Outside.L_meta_3809

theorem PEqualNP.Outside.L_meta_3809 : ∀ (x1 : Fin (9 : ℕ) → Fin (9 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x2.size ∧ ∀ (x5 : Fin (9 : ℕ) → Bool) (x6 x7 : Bool), x4.eval (List.ofFn x5 ++ [x6, x7]) = x2.eval (List.ofFn (x5 ∘ x1) ++ [x6, x7]) := by
  intro f C hC
  refine ⟨{ gates := C.gates.map (PEqualNP.Outside.L_meta_3809.relabelGate f), output := PEqualNP.Outside.L_meta_3809.relabel f C.output }, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hop, hlen⟩ := hC g0 hg0
    exact ⟨hop, by simpa [PEqualNP.Outside.L_meta_3809.relabelGate] using hlen⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x a b
    have h := PEqualNP.Outside.L_meta_3809.rel_fold f C.gates _ _ (PEqualNP.Outside.L_meta_3809.rel_init f x a b)
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    exact (h.2.2 C.output).symm
