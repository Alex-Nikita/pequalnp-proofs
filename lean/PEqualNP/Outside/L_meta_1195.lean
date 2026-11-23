import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1195_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.and, [2, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 7]⟩,
    ⟨.and, [4, 13]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem monotone_witness : Monotone2 witness := by
  simp [Monotone2, witness]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem eval_witness : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    witness.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) ||
       (b2 && b5) || (b3 && b6) || (b4 && b7)) := by
  decide +kernel

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1195_aux

theorem PEqualNP.Outside.L_meta_1195 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1195_aux.witness,
    PEqualNP.Outside.L_meta_1195_aux.monotone_witness, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1195_aux.ofFn8]
  exact PEqualNP.Outside.L_meta_1195_aux.eval_witness
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
