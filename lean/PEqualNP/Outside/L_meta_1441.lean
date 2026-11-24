import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1441

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_start r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem

def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def kept {α : Type} (b : Bool) (x : α) (xs : List α) : List α :=
  if b then x :: xs else xs

inductive Run {α : Type} (inv : α → α) (meet join : α → α → α) (y : α) : ℕ → List α → Prop
  | done : Run inv meet join y 0 [y]
  | perm {s xs zs} : xs.Perm zs → Run inv meet join y s xs → Run inv meet join y s zs
  | one {s a rest} (neg save : Bool) :
      Run inv meet join y s ((if neg then inv a else a) :: kept save a rest) →
      Run inv meet join y (s+1) (a :: rest)
  | two {s a b rest} (conj ka kb : Bool) :
      Run inv meet join y s ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)) →
      Run inv meet join y (s+1) (a :: b :: rest)

theorem kept_map {α β : Type} (e : α → β) (b : Bool) (x : α) (xs : List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e) := by
  cases b <;> simp [kept]

theorem mem_kept {α : Type} (b : Bool) (x a : α) (xs : List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs := by
  cases b <;> simp [kept]

theorem nodup_kept {α : Type} (b : Bool) (x : α) (xs : List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup := by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h

theorem Run.map {α β : Type} (e : α → β) {inv : α → α} {meet join : α → α → α}
    {inv' : β → β} {meet' join' : β → β → β}
    (hi : ∀ a, e (inv a) = inv' (e a)) (hm : ∀ a b, e (meet a b) = meet' (e a) (e b))
    (hj : ∀ a b, e (join a b) = join' (e a) (e b))
    {y : α} {s : ℕ} {ws : List α} (h : Run inv meet join y s ws) :
    Run inv' meet' join' (e y) s (ws.map e) := by
  induction h with
  | done => exact Run.done
  | perm hp _ ih => exact Run.perm (hp.map e) ih
  | @one s a rest neg save _ ih =>
    have e1 : ((if neg then inv a else a) :: kept save a rest).map e
        = (if neg then inv' (e a) else e a) :: kept save (e a) (rest.map e) := by
      cases neg <;> simp [kept_map, hi]
    rw [e1] at ih
    exact Run.one neg save ih
  | @two s a b rest conj ka kb _ ih =>
    have e1 : ((if conj then meet a b else join a b) :: kept ka a (kept kb b rest)).map e
        = (if conj then meet' (e a) (e b) else join' (e a) (e b))
            :: kept ka (e a) (kept kb (e b) (rest.map e)) := by
      cases conj <;> simp [kept_map, hm, hj]
    rw [e1] at ih
    exact Run.two conj ka kb ih

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def val (gs : List Gate) (n : ℕ) (a : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD a false

theorem val_input (gs : List Gate) (n : ℕ) (i : Fin n) : val gs n i = fun x => x i := by
  funext x
  unfold val
  rw [getD_wiresFrom _ _ _ (by simp)]
  simp

theorem val_gate (n : ℕ) (gs : List Gate) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hlt : ∀ a ∈ g.inputs, a < n + p) (x : Fin n → Bool) :
    val gs n (n + p) x = g.op.eval (g.inputs.map fun a => val gs n a x) := by
  obtain ⟨pre, post, rfl, hlen⟩ := split_at gs p g hp
  unfold val
  have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
      (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre (List.ofFn x)).length = n + p := by
    rw [length_wiresFrom]; simp [hlen]
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hal := hlt a ha
  have e1 := getD_wiresFrom post (wiresFrom pre (List.ofFn x) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) a
        (by simp [hl]; omega)
  rw [e1, List.getD_append _ _ _ _ (by omega)]

def shift (K a : ℕ) : ℕ := if a < K then a else a - 1

def shGate (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift K)⟩

def RelD (K : ℕ) (W W' : List Bool) : Prop :=
  W.length = W'.length + 1 ∧ K ≤ W'.length ∧
    ∀ a, a ≠ K → W'.getD (shift K a) false = W.getD a false

theorem relD_wires (K : ℕ) (post : List Gate) : ∀ W W' : List Bool,
    (∀ g ∈ post, K ∉ g.inputs) → RelD K W W' →
    RelD K (wiresFrom post W) (wiresFrom (post.map (shGate K)) W') := by
  induction post with
  | nil => intro W W' _ h; exact h
  | cons g post ih =>
    intro W W' hno h
    obtain ⟨h1, h2, h3⟩ := h
    have hv : (shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [shGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun e => hno g List.mem_cons_self (e ▸ ha))
    have s1 : wiresFrom (g :: post) W
        = wiresFrom post (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl
    have s2 : wiresFrom ((g :: post).map (shGate K)) W'
        = wiresFrom (post.map (shGate K))
          (W' ++ [(shGate K g).op.eval ((shGate K g).inputs.map fun i => W'.getD i false)]) := rfl
    rw [s1, s2, hv]
    apply ih _ _ (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    refine ⟨by simp; omega, by simp; omega, ?_⟩
    intro a haK
    rcases Nat.lt_trichotomy a W.length with hw | hw | hw
    · have hlt : shift K a < W'.length := by
        unfold shift; split <;> omega
      rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
      exact h3 a haK
    · have he : shift K a = W'.length := by
        unfold shift; split <;> omega
      rw [he, hw, getD_snoc_eq, getD_snoc_eq]
    · have hge : W'.length + 1 ≤ shift K a := by
        unfold shift; split <;> omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem del_gate (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (o : ℕ) (f : BFn n)
    (hok : ∀ g' ∈ pre ++ g :: post, Ok g')
    (hno : ∀ g' ∈ post, n + pre.length ∉ g'.inputs) (ho : o ≠ n + pre.length)
    (hev : ∀ x, val (pre ++ g :: post) n o x = f x) :
    HasCircuitSize n f (pre.length + post.length) := by
  refine ⟨⟨pre ++ post.map (shGate (n + pre.length)), shift (n + pre.length) o⟩, ?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hok g' (List.mem_append_left _ h)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
      have := hok g0 (List.mem_append_right _ (List.mem_cons_of_mem _ hg0))
      exact ⟨this.1, by simpa [shGate] using this.2⟩
  · simp [Circuit.size]
  · intro x
    rw [← hev x]
    show (wiresFrom (pre ++ post.map (shGate (n + pre.length))) (List.ofFn x)).getD
      (shift (n + pre.length) o) false = _
    unfold val
    have h1 : wiresFrom (pre ++ g :: post) (List.ofFn x) = wiresFrom post
        (wiresFrom pre (List.ofFn x) ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]) := by
      rw [wiresFrom_append]; rfl
    have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
      rw [length_wiresFrom]; simp
    rw [h1, wiresFrom_append]
    refine (relD_wires (n + pre.length) post _ _ hno ⟨by simp, by omega, ?_⟩).2.2 o ho
    intro a ha
    by_cases hlt : a < n + pre.length
    · have : shift (n + pre.length) a = a := by simp [shift, hlt]
      rw [this, List.getD_append _ _ _ _ (by omega)]
    · have : shift (n + pre.length) a = a - 1 := by simp [shift, hlt]
      rw [this, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

def Live (gs : List Gate) (o p a : ℕ) : Prop :=
  a = o ∨ ∃ q, p ≤ q ∧ ∃ g, gs[q]? = some g ∧ a ∈ g.inputs

open Classical in
noncomputable def liveList (gs : List Gate) (n o p : ℕ) : List ℕ :=
  (List.range (n + p)).filter (fun a => decide (Live gs o p a))

theorem mem_liveList (gs : List Gate) (n o p a : ℕ) :
    a ∈ liveList gs n o p ↔ a < n + p ∧ Live gs o p a := by
  simp [liveList]

theorem nodup_liveList (gs : List Gate) (n o p : ℕ) : (liveList gs n o p).Nodup :=
  List.Nodup.filter _ List.nodup_range

abbrev invF {n : ℕ} : BFn n → BFn n := fun a x => !a x
abbrev meetF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x && b x
abbrev joinF {n : ℕ} : BFn n → BFn n → BFn n := fun a b x => a x || b x

theorem live_succ (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (a : ℕ) :
    a ∈ liveList gs n o (p + 1) ↔
      a = n + p ∨ (a ∈ liveList gs n o p ∧ (a ∈ g.inputs → Live gs o (p + 1) a)) := by
  have hplt : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rw [mem_liveList, mem_liveList]
  constructor
  · rintro ⟨hlt, hl⟩
    by_cases ha : a = n + p
    · exact Or.inl ha
    · refine Or.inr ⟨⟨by omega, ?_⟩, fun _ => hl⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, by omega, g', hg', hin⟩
  · rintro (rfl | ⟨⟨hlt, hl⟩, himp⟩)
    · refine ⟨by omega, ?_⟩
      rcases hnd p hplt with h | ⟨q, g', hg', hin⟩
      · exact Or.inl h
      · refine Or.inr ⟨q, ?_, g', hg', hin⟩
        have := (hcl q g' hg').lt _ hin
        omega
    · refine ⟨by omega, ?_⟩
      rcases hl with h | ⟨q, hq, g', hg', hin⟩
      · exact Or.inl h
      · by_cases hqp : q = p
        · subst hqp
          rw [hg] at hg'
          cases hg'
          exact himp hin
        · exact Or.inr ⟨q, by omega, g', hg', hin⟩

open Classical in
theorem run_live (n : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL n gs) (ho : o < n + gs.length)
    (hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∀ d p, p + d = gs.length →
      Run (invF (n := n)) meetF joinF (val gs n o) d ((liveList gs n o p).map (val gs n)) := by
  intro d
  induction d with
  | zero =>
    intro p hp
    have hperm : [o].Perm (liveList gs n o p) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (nodup_liveList _ _ _ _)).2 ?_
      intro a
      rw [mem_liveList, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨by omega, Or.inl rfl⟩
      · rintro ⟨_, h | ⟨q, hq, g', hg', _⟩⟩
        · exact h
        · have := (List.getElem?_eq_some_iff.1 hg').1
          omega
    exact Run.perm (hperm.map (val gs n)) Run.done
  | succ d ih =>
    intro p hp
    have hplt : p < gs.length := by omega
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hplt⟩
    have IH := ih (p + 1) (by omega)
    have hstep := live_succ n gs o hcl hnd p g hg
    have hin : ∀ a ∈ g.inputs, a ∈ liveList gs n o p := fun a ha =>
      (mem_liveList _ _ _ _ _).2 ⟨(hcl p g hg).lt a ha, Or.inr ⟨p, le_rfl, g, hg, ha⟩⟩
    have hnew : ∀ a ∈ liveList gs n o p, a ≠ n + p := fun a ha =>
      Nat.ne_of_lt ((mem_liveList _ _ _ _ _).1 ha).1
    have hvg := val_gate n gs p g hg (hcl p g hg).lt
    have hnd0 := nodup_liveList gs n o p
    
    have single : ∀ (j : ℕ) (neg : Bool), (∀ a, a ∈ g.inputs ↔ a = j) →
        val gs n (n + p) = (if neg then invF (val gs n j) else val gs n j) →
        Run (invF (n := n)) meetF joinF (val gs n o) (d + 1)
          ((liveList gs n o p).map (val gs n)) := by
      intro j neg hmem hval
      have hj := hin j ((hmem j).2 rfl)
      have hp1 : (liveList gs n o p).Perm (j :: (liveList gs n o p).erase j) :=
        List.perm_cons_erase hj
      have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
      have hp2 : (liveList gs n o (p + 1)).Perm
          ((n + p) :: kept (decide (Live gs o (p + 1) j)) j ((liveList gs n o p).erase j)) := by
        refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
        · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
          rw [mem_kept]
          rintro (⟨_, h⟩ | h)
          · exact hnew j hj h.symm
          · exact hnew _ (List.mem_of_mem_erase h) rfl
        · intro a
          rw [hstep a, List.mem_cons, mem_kept, hnd0.mem_erase_iff, hmem a]
          simp only [decide_eq_true_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · by_cases haj : a = j
              · exact Or.inr (Or.inl ⟨haj ▸ h2 haj, haj⟩)
              · exact Or.inr (Or.inr ⟨haj, h1⟩)
          · rintro (h | ⟨h1, rfl⟩ | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨hj, fun _ => h1⟩
            · exact Or.inr ⟨h2, fun h => absurd h h1⟩
      have IH' := Run.perm (hp2.map (val gs n)) IH
      rw [List.map_cons, kept_map, hval] at IH'
      exact Run.perm (hp1.map (val gs n)).symm (Run.one neg _ IH')
    rcases hcl p g hg with ⟨hop, j, hj, hinp⟩ | ⟨hop, j, k, hj, hk, hinp⟩
    · apply single j true
      · intro a; simp [hinp]
      · funext x
        rw [hvg x, hop, hinp]
        simp [GateOp.eval]
    · by_cases hjk : j = k
      · subst hjk
        apply single j false
        · intro a; simp [hinp]
        · funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
      · have hjm := hin j (by simp [hinp])
        have hkm := hin k (by simp [hinp])
        have hke : k ∈ (liveList gs n o p).erase j :=
          (hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm, hkm⟩
        have hnr : ((liveList gs n o p).erase j).Nodup := hnd0.erase j
        have hnr2 : (((liveList gs n o p).erase j).erase k).Nodup := hnr.erase k
        have hp1 : (liveList gs n o p).Perm
            (j :: k :: ((liveList gs n o p).erase j).erase k) :=
          (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
        have hmr : ∀ a, a ∈ ((liveList gs n o p).erase j).erase k ↔
            a ≠ k ∧ a ≠ j ∧ a ∈ liveList gs n o p := by
          intro a
          rw [hnr.mem_erase_iff, hnd0.mem_erase_iff]
        have hp2 : (liveList gs n o (p + 1)).Perm
            ((n + p) :: kept (decide (Live gs o (p + 1) j)) j
              (kept (decide (Live gs o (p + 1) k)) k
                (((liveList gs n o p).erase j).erase k))) := by
          refine (List.perm_ext_iff_of_nodup (nodup_liveList _ _ _ _) ?_).2 ?_
          · refine List.nodup_cons.2 ⟨?_, nodup_kept _ _ _ (nodup_kept _ _ _ hnr2 ?_) ?_⟩
            · rw [mem_kept, mem_kept]
              rintro (⟨_, h⟩ | ⟨_, h⟩ | h)
              · exact hnew j hjm h.symm
              · exact hnew k hkm h.symm
              · exact hnew _ ((hmr _).1 h).2.2 rfl
            · rw [hmr]; simp
            · rw [mem_kept, hmr]
              rintro (⟨_, h⟩ | h)
              · exact hjk h
              · exact h.2.1 rfl
          · intro a
            rw [hstep a, List.mem_cons, mem_kept, mem_kept, hmr a]
            simp only [decide_eq_true_eq, hinp, List.mem_cons, List.not_mem_nil, or_false]
            constructor
            · rintro (h | ⟨h1, h2⟩)
              · exact Or.inl h
              · by_cases haj : a = j
                · exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj), haj⟩)
                · by_cases hak : a = k
                  · exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak), hak⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨hak, haj, h1⟩))
            · rintro (h | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, h3⟩)
              · exact Or.inl h
              · exact Or.inr ⟨hjm, fun _ => h1⟩
              · exact Or.inr ⟨hkm, fun _ => h1⟩
              · exact Or.inr ⟨h3, fun h => by rcases h with h | h <;> contradiction⟩
        have IH' := Run.perm (hp2.map (val gs n)) IH
        have hval : val gs n (n + p) = (if decide (g.op = GateOp.and)
            then meetF (val gs n j) (val gs n k) else joinF (val gs n j) (val gs n k)) := by
          funext x
          rw [hvg x, hinp]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
        rw [List.map_cons, kept_map, kept_map, hval] at IH'
        exact Run.perm (hp1.map (val gs n)).symm (Run.two _ _ _ IH')

theorem exists_run {n : ℕ} (f : BFn n) (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (s : ℕ)
    (h : HasCircuitSize n f s) :
    ∃ s', s' ≤ s ∧ ∃ ws : List (BFn n),
      ws.Sublist (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i)) ∧
      Run (invF (n := n)) meetF joinF f s' ws := by
  classical
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length = t ∧
    ∀ x, val gs n o x = f x
  have hP : ∀ t, HasCircuitSize n f t → ∃ t', t' ≤ t ∧ P t' := by
    intro t ht
    obtain ⟨gs, o, hcl, hsz, hev⟩ := clean_of n f t hnc ht
    exact ⟨gs.length, hsz, gs, o, hcl, rfl, hev⟩
  obtain ⟨t0, ht0, hPt0⟩ := hP s h
  have hex : ∃ t, P t := ⟨t0, hPt0⟩
  have hmin : Nat.find hex ≤ t0 := Nat.find_min' hex hPt0
  obtain ⟨gs, o, hcl, hlen, hev⟩ := Nat.find_spec hex
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have ho : o < n + gs.length := by
    by_contra hge
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hev y, ← hev y']
    unfold val
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega),
      List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)]
  have hnd : ∀ p, p < gs.length → n + p = o ∨ ∃ (q : ℕ) (g : Gate), gs[q]? = some g ∧ n + p ∈ g.inputs := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    obtain ⟨hpo, hno⟩ := hcon
    obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨pre, post, rfl, hpl⟩ := split_at gs p g hg
    have hsz := del_gate n pre g post o f hok (by
      intro g' hg'
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg'
      have := hno (pre.length + 1 + q) g' (by
        rw [List.getElem?_append_right (by omega)]
        have e : pre.length + 1 + q - pre.length = q + 1 := by omega
        rw [e]; simpa using hq)
      rw [hpl]; exact this) (by rw [hpl]; exact fun e => hpo e.symm) hev
    obtain ⟨t', ht', hPt'⟩ := hP _ hsz
    have := Nat.find_min' hex hPt'
    simp at hlen
    omega
  refine ⟨gs.length, by omega, (liveList gs n o 0).map (val gs n), ?_, ?_⟩
  · have e : (List.ofFn fun (i : Fin n) => (fun x : Fin n → Bool => x i))
        = (List.range n).map (val gs n) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
        exact (val_input gs n ⟨i, by simpa using h1⟩).symm
    rw [e]
    exact (List.filter_sublist).map _
  · have hf : val gs n o = f := funext hev
    rw [← hf]
    exact run_live n gs o hcl ho hnd gs.length 0 (by omega)





theorem run_len {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
    xs.length ≤ s + 1 := by
  induction h with
  | done => simp
  | perm hp _ ih => rwa [←hp.length_eq]
  | one neg save h ih => cases save <;> simp_all [kept] <;> omega
  | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [kept] <;> omega

abbrev NatRun (m : Nat) := Run (· ^^^ m) (· &&& ·) (· ||| ·)

theorem run_bits {m y s xs} (h : NatRun m y s xs) (i j : Nat)
    (hm : m.testBit i = m.testBit j)
    (hw : ∀ w ∈ xs, w.testBit i = w.testBit j) : y.testBit i = y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih => exact ih (fun w h => hw w (hp.mem_iff.1 h))
  | one neg save h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    intro w hmem
    cases neg <;> cases save <;> simp only [Bool.false_eq_true, ite_false, ite_true,
      kept, List.mem_cons] at hmem <;>
      first | (rcases hmem with rfl | hr; exact ha; exact hw _ (by simp [hr]))
            | (rcases hmem with rfl | hr; simp [ha,hm]; exact hw _ (by simp [hr]))
  | two conj ka kb h ih =>
    apply ih
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hmem
    cases conj <;> cases ka <;> cases kb <;> simp only [Bool.false_eq_true,
      ite_false, ite_true, kept, List.mem_cons] at hmem <;>
      rcases hmem with rfl | hr <;> first | simp [ha,hb] | exact hw _ (by simp only [List.mem_cons]; tauto)

def diff (k w : Nat) : Nat := w ^^^ (w >>> k)

def cov (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diff k a ||| cov k t

theorem cov_bit (k i : Nat) (ws : List Nat) : (cov k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i ≠ a.testBit (k+i) := by
  induction ws with
  | nil => simp [cov]
  | cons a t ih =>
    simp only [cov, Nat.testBit_or, Bool.or_eq_true, ih, diff, Nat.testBit_xor,
      Nat.testBit_shiftRight, List.mem_cons]
    cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all

def lo (k : Nat) := 2^k - 1
def mask (k : Nat) := lo (k+k)
def goal (k : Nat) := lo k <<< k

theorem required {k s ws} (h : NatRun (mask k) (goal k) s ws) :
    (cov k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hm : (mask k).testBit i = (mask k).testBit (k+i) := by
      simp [mask,lo,Nat.testBit_two_pow_sub_one,show i < k+k by omega,show k+i < k+k by omega]
    have hy : (goal k).testBit i ≠ (goal k).testBit (k+i) := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (cov k ws).testBit i = true := by
      apply (cov_bit k i ws).2
      by_contra! hh
      exact hy (run_bits h i (k+i) hm hh)
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def keep_perm {α : Type} {xs ys : List α} (p : xs.Perm ys) (b : Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys) := by cases b <;> simpa [kept] using p

def tagU (ws : List Nat) (a : Nat) (neg ka : Bool) :=
  4 * ws.idxOf a + 2 * neg.toNat + ka.toNat

def tagB (ws : List Nat) (a b : Nat) (conj ka kb : Bool) :=
  let j := ws.idxOf b
  48 + 8 * (j*(j+1)/2 + ws.idxOf a) + 4 * conj.toNat + 2 * ka.toNat + kb.toNat

def next (m : Nat) (slack : Nat) (ws : List Nat) (f : Nat → List Nat → Bool) : Bool :=
  ws.any fun a =>
    let ra := ws.erase a
    (slack ≥ 1 && ([false,true].any fun neg =>
      let w := if neg then a ^^^ m else a
      f (tagU ws a neg false) (w :: ra) || (slack ≥ 2 && f (tagU ws a neg true) (w :: a :: ra)))) ||
    ra.any fun b =>
      a ≤ b && (let r := ra.erase b
        [false,true].any fun conj =>
          let w := if conj then a &&& b else a ||| b
          f (tagB ws a b conj false false) (w :: r) || (slack ≥ 1 && (f (tagB ws a b conj true false) (w :: a :: r) || f (tagB ws a b conj false true) (w :: b :: r))) ||
            (slack ≥ 2 && f (tagB ws a b conj true true) (w :: a :: b :: r)))

theorem next_one {k a rest} {neg save : Bool} {s ws} (p : (a :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s ((if neg then a ^^^ mask k else a) :: kept save a rest))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pr : rest.Perm (ws.erase a) := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  have hsl : 1 ≤ s+2-ws.length := by cases save <;> simp [kept] at hh <;> omega
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; left
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hsl,?_⟩
  apply List.any_eq_true.2 ⟨neg,by cases neg <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm pr save a).cons _) h)
  cases save with
  | false => simp [kept] at ht; simp [ht]
  | true =>
    simp [kept] at ht hh
    have hsl2 : 2 ≤ s+2-ws.length := by omega
    simp [ht,hsl2]

theorem next_two_sorted {k a b rest} {conj ka kb : Bool} {s ws} (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  have ha := p.mem_iff.1 List.mem_cons_self
  have pp := (p.trans (List.perm_cons_erase ha)).cons_inv
  have hb := pp.mem_iff.1 List.mem_cons_self
  have pr := (pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh := run_len h
  have hl := p.length_eq
  simp only [List.length_cons] at hl hh
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  rw [Bool.or_eq_true]; right
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨conj,by cases conj <;> simp,?_⟩
  have ht (t : Nat) := hf t _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht, Bool.true_or, Bool.or_true, Bool.and_true, Bool.true_and] <;>
    first | (simp [show 2 ≤ s+2-ws.length by omega]) | (simp [show 1 ≤ s+2-ws.length by omega])

theorem next_two {k a b rest} {conj ka kb : Bool} {s ws}
    (p : (a :: b :: rest).Perm ws)
    (h : NatRun (mask k) (goal k) s
      ((if conj then a &&& b else a ||| b) :: kept ka a (kept kb b rest)))
    (f : Nat → List Nat → Bool)
    (hf : ∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) :
    next (mask k) (s+2-ws.length) ws f = true := by
  rcases le_total a b with hab | hba
  · exact next_two_sorted hab p h f hf
  · apply next_two_sorted (conj:=conj) (ka:=kb) (kb:=ka) hba ((List.Perm.swap _ _ _).trans p) _ f hf
    have he : (if conj then a &&& b else a ||| b) = (if conj then b &&& a else b ||| a) := by
      cases conj <;> simp [Nat.and_comm, Nat.or_comm]
    rw [he] at h
    apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]
    exact List.Perm.swap _ _ _

theorem zero_done {α inv meet join y t ws} (h : @Run α inv meet join y t ws) :
    t = 0 → ws = [y] := by
  induction h with
  | done => simp
  | perm p h ih => intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | one => simp
  | two => simp

theorem next_complete {k t ws} (h : NatRun (mask k) (goal k) t ws) :
    ∀ s, t = s+1 → ∀ zs, ws.Perm zs → ∀ f : Nat → List Nat → Bool,
      (∀ (t : Nat) ys, NatRun (mask k) (goal k) s ys → f t ys = true) →
      next (mask k) (s+2-zs.length) zs f = true := by
  induction h with
  | done => simp
  | perm p h ih => intro s he zs q; exact ih s he zs (p.trans q)
  | one neg save h ih => intro s he zs p f hf; cases he; exact next_one p h f hf
  | two conj ka kb h ih => intro s he zs p f hf; cases he; exact next_two p h f hf




open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], j => by simp [encL]
  | v :: t, 0 => by simp [encL, Nat.testBit_bit_zero]
  | v :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_inv {n : ℕ} (a : BFn n) (l : List ℕ) :
    encL (invF a) l = encL a l ^^^ (2 ^ l.length - 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp [h]

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (meetF a b) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (joinF a b) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

def blockWord (d : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | q::r, w => ((w >>> (d*q)) &&& lo d) ||| (blockWord d r w <<< d)

theorem block_hom (d : Nat) (qs : List Nat) (a b : Nat) :
    blockWord d qs (a &&& b) = (blockWord d qs a &&& blockWord d qs b) ∧
    blockWord d qs (a ||| b) = (blockWord d qs a ||| blockWord d qs b) ∧
    blockWord d qs (a ^^^ b) = (blockWord d qs a ^^^ blockWord d qs b) := by
  induction qs with
  | nil => simp [blockWord]
  | cons q qs ih =>
    refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro j <;>
      by_cases hj : d ≤ j <;>
      simp [blockWord,lo,Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, hj, ih,
        Nat.not_lt_of_ge, Nat.lt_of_not_ge] <;> grind

theorem block_run {s ws k} (h : NatRun (mask k) (goal k) s ws)
    (d : Nat) (qs : List Nat) (hm : blockWord d qs (mask k) = mask k)
    (hg : blockWord d qs (goal k) = goal k) :
    NatRun (mask k) (goal k) s (ws.map (blockWord d qs)) := by
  rw [← hg]
  exact Run.map _ (fun a => (block_hom d qs a (mask k)).2.2.trans (by rw [hm]))
    (fun a b => (block_hom d qs a b).1) (fun a b => (block_hom d qs a b).2.1) h





theorem bits_le {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1) (i j : Nat)
    (hw : ∀ a ∈ ws, a.testBit i ≤ a.testBit j) : y.testBit i ≤ y.testBit j := by
  induction h with
  | done => exact hw _ (by simp)
  | perm hp _ ih =>
    exact ih (hp.length_eq.trans hl) (fun a ha => hw a (hp.mem_iff.1 ha))
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    apply ih (by simp [kept]; omega)
    have ha := hw _ List.mem_cons_self
    have hb := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro a had
    simp only [kept, Bool.false_eq_true, ite_false, List.mem_cons] at had
    rcases had with rfl | ht
    · cases conj <;> simp only [ite_true, Bool.false_eq_true, ite_false, Nat.testBit_or,Nat.testBit_and] <;>
        first | exact Bool.or_le_or ha hb | exact Bool.and_le_and ha hb | grind
    · exact hw _ (by simp [ht])

def diffUp (k w : Nat) : Nat := (w >>> k) &&& (w ^^^ lo k)

def covUp (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: t => diffUp k a ||| covUp k t

theorem covUp_bit (k i : Nat) (hi : i < k) (ws : List Nat) : (covUp k ws).testBit i = true ↔
    ∃ a ∈ ws, a.testBit i = false ∧ a.testBit (k+i) = true := by
  induction ws with
  | nil => simp [covUp]
  | cons a t ih =>
    simp [covUp, diffUp, lo, hi, ih, and_comm]

theorem required_up {k s ws} (h : NatRun (mask k) (goal k) s ws) (hl : ws.length = s+1) :
    (covUp k ws &&& lo k) = lo k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < k
  · have hy : ¬ (goal k).testBit (k+i) ≤ (goal k).testBit i := by
      simp [goal,lo,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hi,show ¬ k ≤ i by omega]
    have hc : (covUp k ws).testBit i = true := by
      apply (covUp_bit k i hi ws).2
      by_contra! hh
      apply hy
      apply bits_le h hl
      intro a ha
      specialize hh a ha
      cases hx : a.testBit i <;> cases hy : a.testBit (k+i) <;> simp_all
    simp [hc]
  · simp [lo,Nat.testBit_two_pow_sub_one,hi]

def covers (k s : Nat) (ws : List Nat) : Bool :=
  if ws.length == s+1 then covUp k ws &&& lo k == lo k else cov k ws &&& lo k == lo k

theorem covers_ok {k s ws} (h : NatRun (mask k) (goal k) s ws) : covers k s ws = true := by
  by_cases he : ws.length = s+1
  · simp [covers,he,required_up h he]
  · simp [covers,he,required h]





def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem score_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (v : Nat → Nat) (hand : ∀ a b, v (a &&& b) ≤ v a + v b)
    (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    v y ≤ (ws.map v).sum := by
  induction h with
  | done => simp
  | perm p h ih =>
    rw [← (p.map v).sum_eq]
    exact ih (p.length_eq.trans hl)
  | one neg save h ih =>
    have hh := run_len h
    cases save <;> simp [kept] at hh hl <;> omega
  | two conj ka kb h ih =>
    have hh := run_len h
    cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih' := ih (by simp [kept]; omega)
    cases conj <;> simp [kept] at ih' ⊢ <;> first | grw [← Nat.add_assoc, ← hand]; exact ih' | grw [← Nat.add_assoc, ← hor]; exact ih'

def eval6 (a b c d e f v : Nat) := value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)

theorem eval6_bound {m y s ws} (h : NatRun m y s ws) (hl : ws.length = s+1)
    (a b c d e f : Nat) : eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum := by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,Nat.testBit_and] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,Nat.testBit_or] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

def scoreCheck (k s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    let a := code &&& 1023
    let b := (code >>> 10) &&& 1023
    let c := (code >>> 20) &&& 1023
    let d := (code >>> 30) &&& 1023
    let e := (code >>> 40) &&& 1023
    let f := (code >>> 50) &&& 1023
    ws.length == s+1 && (ws.map (eval6 a b c d e f)).sum < eval6 a b c d e f (goal k)

theorem scoreCheck_no {k s ws} (h : NatRun (mask k) (goal k) s ws) (code : Nat) :
    scoreCheck k s ws code = false := by
  unfold scoreCheck
  split
  · rfl
  · dsimp only
    by_cases hl : ws.length = s+1
    · simp [hl,Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _)]
    · simp [hl]





def unpackWords (wt : Nat → Nat) (bits : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | t+1, v => if v = 0 then [] else
      wt (v &&& (2^bits-1)) :: unpackWords wt bits t (v >>> bits)

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n+1, i => f i && span f n (i+1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o+n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o+a) = true) :
    span f (a+b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb)⟩

theorem extend_run {α inv meet join y s t a r} (h : @Run α inv meet join y s (a::r))
    (hle : s ≤ t) : Run inv meet join y t (a::r) := by
  induction t, hle using Nat.le_induction with
  | base => exact h
  | succ t hle ih => exact Run.one false false ih





def edgeHash : List Nat → Nat
  | [] => 0
  | w :: t => (w % 4294967291 + 317)^3 % 4294967291 + 1 + edgeHash t

def barrier (k : Nat) (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (act : Nat → Nat → Nat → Nat) (wits : Nat → Nat)
    (rot : Nat → List Nat → List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(next (mask k) (s+2-ws.length) ws fun tag zs =>
        covers k s zs && (
          let v := act (s+1) i tag
          if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
          else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16)))))

theorem barrier_sound {k S N act wits rot} {s i} (hb : barrier k S N act wits rot s i = true)
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (h : NatRun (mask k) (goal k) s (S s i)) :
    ∃ q < s, ∃ j < N q, NatRun (mask k) (goal k) q (S q j) := by
  cases s with
  | zero => simp [barrier,zero_done h rfl] at hb
  | succ s =>
    by_contra! hn
    let F (tag : Nat) (zs : List Nat) := covers k s zs && (
      let v := act (s+1) i tag
      if v % 2 = 1 then !scoreCheck k s zs (wits (v/2))
      else !(v/16 < N s && (rot (v/2 % 8) zs).isPerm (S s (v/16))))
    have hF (tag : Nat) (zs) (hz : NatRun (mask k) (goal k) s zs) : F tag zs = true := by
      simp only [F,covers_ok hz,Bool.true_and]
      split
      · simp [scoreCheck_no hz]
      · simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
        intro hj
        by_contra! hp
        have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact hn s (by omega) _ hj (Run.perm p (hr _ hz))
    have hN := next_complete h s rfl _ (List.Perm.refl _) F hF
    change !(next _ _ _ F) = true at hb
    rw [hN] at hb
    contradiction

theorem barrier_all {k S N act wits rot} {cap : Nat}
    (hr : ∀ g {u ys}, NatRun (mask k) (goal k) u ys → NatRun (mask k) (goal k) u (rot g ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, barrier k S N act wits rot s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ NatRun (mask k) (goal k) s (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    obtain ⟨q,hq,j,hj,h⟩ := barrier_sound (hc s hs i hi) hr hh
    exact ih q hq (by omega) j hj h




def idRot (_ : ℕ) (ws : List ℕ) : List ℕ := ws

def unpackW (wt : List ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, p => if p = 0 then [] else wt.getD (p % 1024 - 1) 0 :: unpackW wt fuel (p / 1024)

def findAct : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, p, tag => if p = 0 then 0 else
      if p % 512 = tag then p / 512 % 16384 else findAct fuel (p / 8388608) tag

def rowsT0 : List ℕ := [1, 1, 2, 3, 3, 3, 4, 5, 5, 5, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 9, 17, 6, 7, 11, 19, 6, 7, 13, 21, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT0 : List ℕ := [0x9327dd80003bb, 0x12e5c7e01c383c, 0x274e9e60e1c3c0, 0x3c8fe88f01fc00, 0x3ff91117fe0000]

abbrev fT0 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT0 : List ℕ := [0x6eee801ffff, 0x2045c0000038, 0x1021c40000380, 0x2448660000000, 0x3701770fe03ff, 0x8026888000000, 0x9301110000000, 0x9327998000000, 0x9327dd80003bb, 0xb76fff80003bb, 0x1085c080003800, 0x12c5c6e0003800, 0x12e101001c0000, 0x12e587601c0000, 0x12e5c7e01c383c, 0x18b1619f1e3c3f, 0x1ae7efe81c383c, 0x1bf5d7f01c383c, 0x1bf7fff81c3bbf, 0x240e880001c000, 0x264e8e6001c000, 0x27481000e00000, 0x274c9660e00000, 0x274e9e60e1c3c0, 0x2d1a381fe3c7c3, 0x2f4efee8e1c3c0, 0x2f7e9f70e1c3c0, 0x2f7efff8e1c3fb, 0x36cd8227fffc44, 0x37efdfe0fdfbfc, 0x3c890007000000, 0x3c8b688f000000, 0x3c8fe88f01fc00, 0x3db91117000000, 0x3dbff99f01fc00, 0x3dbffddf01ffbb, 0x3ecfeeef01fc00, 0x3eefefef1dfc3c, 0x3fcffeefe1ffc0, 0x3ff91117fe0000, 0x3ffb799ffe0000, 0x3ffb7ddffe03bb, 0x3ffd9777fe0000, 0x3ffdd7f7fe383c, 0x3fff9f77ffc3c0, 0x3ffff99ffffc00]

def levT0 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x881803c06, 0x801803c07, 0x7c1803c08],
  [0x280841803c09, 0x280841d0600f, 0x280841906009, 0x280841003c09, 0x280600f02405, 0x210600f02401, 0x280841d06418, 0x280841d0400f, 0x280741803c05, 0x210741803c01, 0x280841804c02, 0x280841c03c03, 0x280901803c06, 0x220841803c09, 0x280841804409, 0x280841a03c09, 0x290841803c09, 0x2a0841803c07, 0x280801803c09, 0x280841804809, 0x280841b03c09, 0x2808c1803c09, 0x280841904009, 0x280641802405, 0x210641802401, 0x280841e02404, 0x280841803c0a, 0x280941803c09, 0x2b0841803c09, 0x280981802c09, 0x280841503c09, 0x2c0841803409, 0x280841703c09, 0x280400f02405, 0x210400f02401, 0x280841803009, 0x2809c1403c09, 0x280841803809, 0x2d0841603c09, 0x1803c0901401, 0x280841803c08, 0x2e07c1803c09],
  [0x280841803c09, 0xa0210600f02409, 0x280841d0600f, 0xa0210741803c09, 0xa0210601303c09, 0xa0210600f02402, 0xa0210701803c09, 0xa0210600f02403, 0xa0240841803c09, 0xa0210600f02406, 0xa8280841803c09, 0xa0210600f02407, 0xa0210600f03c09, 0x280841906009, 0xa0210641803c09, 0xa0210781803c09, 0xa0210600f02404, 0xa0260841803c09, 0xa0210600f02c09, 0xb0280841803c09, 0xa0210600f03409, 0xa0210601803c09, 0x280841003c09, 0xa0210601003c09, 0xa0270841803c09, 0xa0210601403c09, 0xb4280841803c09, 0xa0210601603c09, 0xa0210841803c09, 0x280600f02405, 0xa0210600f02405, 0xb8280841803c09, 0xa02107c1803c09, 0xa0280841803c09, 0x210600f02401, 0xa0210600f02401],
  [0x280841803c09]]

def actT0 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x259880552500a63a01141802282004502008a00, 0x1598802b2500563a00ac1801582002b02005600, 0x9880012500023a00041800082000102000200],
  [0x610000c1800182000302000600, 0x60a, 0x60a, 0x60a, 0x602, 0x602, 0x0, 0x0, 0x0, 0x0, 0xc8f40191d00321000641800c82001902003200, 0xf93401f25003e10007c1800f82001f02003e00, 0x8a9e01153a00027004b41008a650114c40249280471d008a1001141802282004502008a00, 0x2990004cc0139940003200121000241800482000902001200, 0x3610006c1800d82001b02003600, 0x521000a41801482002902005200, 0x53a000a140013100021000041800082000102000200, 0x9a9e00ad3a00827002b4280568200acc401592802b1d00561000ac1801582002b02005600, 0x29a00050c015a1401042001610002c1800582000b02001600, 0x610000c1800182000302000600, 0x221000441800882001102002200, 0x53c000a080013280021000041800082000102000200, 0x0, 0x0, 0x0, 0x695000d0400a9d400331000a52000c9a0019280031d000610000c1800182000302000600, 0x610000c1800182000302000600, 0x6750044da0039280051d000610000c1800182000302000600, 0x695000d1a0039280051d000610000c1800182000302000600, 0xc4ea0189b40313500621000c41801882003102006200, 0xce40279b40051d000610000c1800182000302000600, 0xdd2a01ba3403745006e1000dc1801b82003702006e00, 0xd24001a340051d000610000c1800182000302000600, 0x0, 0x0, 0x144ea0089a80072500221000441800882001102002200, 0xe4ea01c9c80393680721000e41801c82003902007200, 0x10d2a001a2800725000610000c1800182000302000600, 0x1052a020a480414680821001041802082004102008200, 0x0, 0x53c000a740204e0002820004c40009280011d00021000041800082000102000200, 0xa740014d00028600050a0102100013100021000041800082000102000200],
  [0x53e000a6c0034b800693000d1e001a2c00143801683000cee0099cc01137801e6b0004ce00498c0032b800653000c9e00392c0031f800a3b000c2602804800308800010000c1e0200380150680000c000c160180280030480000800340e01001800302800004000c0600800800100800000, 0x55a005aa400142801281000cca00398400326800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x480480100801000e00401800182c0000500200801c00c00801006001002000, 0x6c5000d8200aa740154c800676000ce40019b800335000666000cc40018500030800020e000c1800182000302000600, 0xd7a002ae400558802a95000d2200da240033a800a710014da0029840032b000a550000a800294800127000a4d0000980029280171f00323d02807800285000508000a0c000c1400282000502000a00, 0xd5a001aa400342802a81000cca001984017290032510280a0001934003250006490000900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x458a012b040075c80469d004532010a440033b000e750000e80039c800337000a6a0004cc00399400032000e62001cac00e93801f2681604c0014720038500070800060e001c1800382000702000e00, 0xd5a001aa400342802a810074d400f9a40b034000665000cc40019840003000064d000c920018f40031d0002390000700018500030800060c000c1000181000301000600, 0x4b380016681a0cc000d92000b040154f00129d000138004a680034b00229200451c001a2800143001285000108004a0800133004e650300c80048500030900121000241800482000902001200, 0x59a000ad4003568002aa0005520802a000145004e89030110000a1400141002a810001000019940013100526103c0c0001934001250036490380900008f40011d0002390000700008500010800020c00041000081000301000200, 0x1b3800b668000cc002d94000b1800b628240c4000d84001af80255d0006b6001564000ab800b568000ac002d54000a680014300568504410800185800b0a001610002c1800582000b02001600, 0x59c000ac802b588220b000055a000aa8003548000a800051a001a1400141000281054100001994001310022610500c00019340012500064904c0900008f40011d0002390000700008500010800020c00041000081000301000200, 0xd6a001ac401146801e89000cda0019a40032300064500008800190800320800040000c7c0028e80030a000610000c1800681800302000600, 0xc00480200802e00e00801800682c0000500400805800c01001006001004000, 0x1ac5000d82016a740114c8006760034e40019b8003350002660044c400685000d0800060e00341800682000d02001a00, 0xd8a001b040154e801e99000cec0019d40003a000672000cdc0019b40003600066a000ccc0029880032b0006550640a800185000308001a0e000c1800182000302000600, 0xd8a001af4003568006aa000d520e02a00034e802295000d0a001a0801540836080000ce40019c419038000e6a000cca001988003308000600014a4001934003250006490000900018f40031d005e390680700018500030800060c000c1000181000301000600, 0xd9a007b240154f001e9d000138007a680034b001e95078128007a4800347001e8d000118007a2800143000682003ce40189b80333683a06c006c7400785000d09001e10003c1800782000f02001e00, 0x22b5000d62018a480334883a09000451a008a28015448000880044ea0019b4011348022550044a40019440002800063e00d4740088500110800220c00441000181801102002200, 0xd9c001b34000660006ca00558c007b080035f0006bd080178001ae80035b0006b5000168001ac800157000aaa000d2401ba380034683e08c0014740018580030a000610000c1800182000302000600, 0x6eba000d720f82e00035a8006b2000d620002c001146802a89000cea0019b400334800655000ca40019440002800063e00d4740018500030800060c000c1000681800302000600, 0xd7a001ae40034a802691000cbc0019740002e00065a000cb20001600032b000652000c9c0039280030a000610000c1400182000302000600, 0x1100480300804200e00c01800182c0000500600805800c01801007001006000, 0x6bd000d7200aa5400348800675000ce20019580032900024e000c940018500030800060c000c1400182000302000600, 0x459a01eb240154f00269d000138009a680034b002695000128009a480114700268d08c118007a280014300228200e4ec01d9d42403a001e6a00849400985000309002610004c1800982001302002600, 0x6bd000d7201ca6803b4c848098000d2a001a4801548800090000cea0019c800338800070000cdc0019580032900064e00fc940018500030800060c000c1400182000302000600, 0xd9c001b34000660006ca008d8c01eb080035f0006bd000178001ae80035b0006b5094168001ac800157004aaa01052c021a542604a00068a001c940018580030a000610000c1800182000302000600, 0x82c2010d821303000035e8006ba000d720002e00034a802a91000cea0019c800338800070000cdc0019580032900064e00fc940018500030800060c000c1400182000302000600, 0x58a000b040153f002a7d0000f800a9e80153c800078000cec0099c801137001e6a0004cc0049880150a00060e00541800a82001502002a00, 0x1380480400804200e0100180b80280400401000601000800180c00001008000, 0x6ad000d52001a1400340800665000cc20019340032480023d0004720018500030800060c000c1000181001501000600, 0xd9c000b34000660002ca00558c000b14000620002c2000d7c01eae80035b001eb200055c000ab4280560006aa00053c000a742904e0002820004c40018580010a00021000041800082000102000200, 0x1650002c90a4190000b14001610006c1000180000ab80014e80029a005532000260001430006760044e40089b8003350006660004c40008500010800060e00041800082000102000200, 0xd4c001a94000520006a2000d420002800014f00029a000d2c001a480034700068a00050c005a0800309000610000c1800182000302000600, 0x1380480500804400e0140180c00280500401200601400800180c0000100a000, 0x6ad000d5200aa1401540800665000cc20019340032480023d0004720018500030800060c000c1000181000301000600],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT0 : List ℕ := [0x18020602b0a01d, 0x2800048280701b, 0x2c00048280701b, 0x38000542b0701b, 0x600002c2806c1c, 0x6000048280701b, 0x2800048280801b, 0x2803048280701b, 0x28000542b0701b, 0x28070542b0701b, 0x440002c2806c1c, 0x1c1d06c1b, 0x2c000001b06c1b, 0x2c03048280701b, 0xc1d06c1b, 0x38000001b06c1b, 0x38070542b0701b, 0x44000382b06c1c, 0x3800048280701b, 0x280a0601c06c1b, 0x3807048280701b, 0x60000001b06c1b, 0x440002c2807c1c, 0x1c030602b0a01d, 0xc000001b06c1b, 0x28030381d06c1b, 0x540e0001c06c2b, 0xc1c06c1b, 0x1c000001b06c1b, 0x280702c1d06c1b, 0x2807048280701b, 0x480b0001c06c28, 0x1c1c06c1b, 0x28000481d06c1b, 0x601c06c1b, 0xc030601c0701b, 0x1c070601c0701b, 0x60180601c06c1b, 0x60180001c0701b, 0x28000381d06c1b, 0x280002c1d06c1b, 0x8020601c0701b, 0x18060601c0701b]

def S0 (s i : ℕ) : List ℕ := unpackW wdT0 9 ((levT0.getD s []).getD i 0)

def N0 (s : ℕ) : ℕ := (levT0.getD s []).length

def A0 (s i tag : ℕ) : ℕ := findAct 4096 ((actT0.getD s []).getD i 0) tag

def W0 (w : ℕ) : ℕ := witT0.getD w 0

def Z0 (s : ℕ) := barrier 27 S0 N0 A0 W0 idRot s

theorem enc_inputs0 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT0) = xsT0 := by decide +kernel

theorem enc_goal0 : encL fT0 rowsT0 = goal 27 := by decide +kernel

theorem mask0 : mask 27 = 2 ^ rowsT0.length - 1 := by decide +kernel

theorem proper_fail0 : ∀ zs ∈ xsT0.sublists, zs ≠ xsT0 → (cov 27 zs &&& lo 27) ≠ lo 27 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked0 : ∀ s ≤ 7, ∀ i < N0 s, Z0 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun0 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 27) (goal 27) s xsT0) : False := by
  have hc : NatRun (mask 27) (goal 27) 7 xsT0 := extend_run h hs
  have p : xsT0.Perm (S0 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked0 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub0 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT0 → NatRun (mask 27) (goal 27) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT0
  · subst e; exact noRun0 s hs h
  · exact proper_fail0 zs (List.mem_sublists.2 hz) e (required h)

theorem low0 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT0 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT0 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 27) (encL fT0 rowsT0) s' (ws.map fun a => encL a rowsT0) :=
    Run.map (fun a : BFn 5 => encL a rowsT0)
      (fun a => by rw [mask0]; exact encL_inv a rowsT0)
      (fun a b => encL_and a b rowsT0) (fun a b => encL_or a b rowsT0) hrun
  rw [enc_goal0] at hr
  refine no_sub0 s' (by omega) _ ?_ hr
  rw [← enc_inputs0]
  exact hsub.map _

def mono0 : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [10, 11]⟩]

theorem mono_ok0 : ∀ g ∈ mono0, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono0, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval0 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono0, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve0 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono0, 12, mono_ok0, ?_, mono_eval0⟩
  by_contra hlt
  have hlen : mono0.length = 8 := rfl
  apply low0
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT1 : List ℕ := [0, 2, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 1, 3, 5, 7, 14, 22, 9, 11, 14, 26, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT1 : List ℕ := [0x54d33c00000, 0xabaee80e3ba, 0xcd34f330c3c, 0xf23f43c0fc0, 0xffc883ff000]

abbrev fT1 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT1 : List ℕ := [0x54d33c00000, 0xabaee80e3ba, 0xcd34f330c3c, 0xf23f43c0fc0, 0xffc883ff000]

def levT1 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x50100300801]]

def actT1 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x51c000a08001370002620004ac0009280011d00021000041800082000102000200]]

def witT1 : List ℕ := [0x1c030341f06c1a]

def S1 (s i : ℕ) : List ℕ := unpackW wdT1 9 ((levT1.getD s []).getD i 0)

def N1 (s : ℕ) : ℕ := (levT1.getD s []).length

def A1 (s i tag : ℕ) : ℕ := findAct 4096 ((actT1.getD s []).getD i 0) tag

def W1 (w : ℕ) : ℕ := witT1.getD w 0

def Z1 (s : ℕ) := barrier 22 S1 N1 A1 W1 idRot s

theorem enc_inputs1 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT1) = xsT1 := by decide +kernel

theorem enc_goal1 : encL fT1 rowsT1 = goal 22 := by decide +kernel

theorem mask1 : mask 22 = 2 ^ rowsT1.length - 1 := by decide +kernel

theorem proper_fail1 : ∀ zs ∈ xsT1.sublists, zs ≠ xsT1 → (cov 22 zs &&& lo 22) ≠ lo 22 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked1 : ∀ s ≤ 5, ∀ i < N1 s, Z1 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun1 (s : ℕ) (hs : s ≤ 5) (h : NatRun (mask 22) (goal 22) s xsT1) : False := by
  have hc : NatRun (mask 22) (goal 22) 5 xsT1 := extend_run h hs
  have p : xsT1.Perm (S1 5 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked1 5 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub1 : ∀ s ≤ 5, ∀ zs : List ℕ, zs.Sublist xsT1 → NatRun (mask 22) (goal 22) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT1
  · subst e; exact noRun1 s hs h
  · exact proper_fail1 zs (List.mem_sublists.2 hz) e (required h)

theorem low1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT1 5 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT1 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 5 h
  have hr : NatRun (mask 22) (encL fT1 rowsT1) s' (ws.map fun a => encL a rowsT1) :=
    Run.map (fun a : BFn 5 => encL a rowsT1)
      (fun a => by rw [mask1]; exact encL_inv a rowsT1)
      (fun a b => encL_and a b rowsT1) (fun a b => encL_or a b rowsT1) hrun
  rw [enc_goal1] at hr
  refine no_sub1 s' (by omega) _ ?_ hr
  rw [← enc_inputs1]
  exact hsub.map _

def mono1 : List Gate := [⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [7, 8]⟩, ⟨GateOp.or, [0, 9]⟩]

theorem mono_ok1 : ∀ g ∈ mono1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono1, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval1 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono1, 10⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve1 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono1, 10, mono_ok1, ?_, mono_eval1⟩
  by_contra hlt
  have hlen : mono1.length = 6 := rfl
  apply low1
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 5
    omega

def rowsT2 : List ℕ := [1, 1, 1, 1, 2, 2, 4, 4, 8, 10, 10, 10, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 3, 5, 9, 17, 3, 6, 5, 6, 9, 11, 14, 26, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT2 : List ℕ := [0x54d35f00000f, 0xabaeb1038e30, 0xcd34e2cc30c0, 0xf23f04f03f00, 0xffc808ffc000]

abbrev fT2 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT2 : List ℕ := [0x315000f3f, 0x37f7003fff, 0x8211000000, 0xc01903c03f, 0xdc0fb0fc0ff, 0x320b04300f00, 0x32c80833c000, 0x32cb1d33cf3f, 0x441042000000, 0x501304000000, 0x54514efc71cf, 0x54c008000000, 0x54d35f00000f, 0x8924a0000000, 0xa22e00000e00, 0xab2ca0fffff0, 0xab8800038000, 0xabaeb1038e30, 0xc03400c03000, 0xcd0000cc0000, 0xcd34e2000000, 0xcd34e2cc30c0, 0xcd37f7cc3fff, 0xcdb6f3cc30c0, 0xcdf4fbcff0ff, 0xdd37e6cc30c0, 0xddf4eacc30c0, 0xddf7ff00000f, 0xddf7ffcc30cf, 0xefbef3038e30, 0xefbef3cfbef0, 0xf20800f00000, 0xf21b04f00000, 0xf23f04000e00, 0xf23f04f03f00, 0xf2bf15f03f00, 0xf63f46f03f00, 0xf6c808f00000, 0xf6ff0cf03f00, 0xf6ff5ff03f0f, 0xfb3fa4f03f00, 0xfbbfb5038e30, 0xfbbfb5f3bf30, 0xff3ce2fc30c0, 0xff3f04fc3f00, 0xff3fe6fc30c0, 0xff3fe6fc3fc0, 0xffc808038000, 0xffc808ffc000, 0xffca19ffc000, 0xffd84affc000, 0xffdb0cffc000, 0xffdb5fffc00f, 0xffeca8ffc000, 0xffeeb9038e30, 0xffeeb9ffce30, 0xfffc08fff000, 0xfffceafc30c0, 0xfffceafff0c0, 0xffff0cffff00, 0xffffff038e3f]

def levT2 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0xec2f0480d, 0xec2f04810, 0xf43108c18, 0xc4230781d, 0xe8230480d, 0xc42e0480d, 0xec2f0340b, 0xc42307c1c, 0xc42f07012, 0xec2307012, 0xec290480d, 0xd82f0480d, 0xec1203404, 0xbc1203401, 0xe42f0480d, 0xec2d0480d, 0xf02c0480d],
  [0x3108c160480d, 0x3108c1604810, 0x3108c160340b, 0x3108c1203408, 0x310bc160480d, 0x3b08c160480d, 0x310581203405, 0x230581203402, 0x3108c160400b, 0x3108c1204008, 0x310bc1604810, 0x3b08c1604810, 0x310581204005, 0x230581204002, 0x3d0c42305803, 0x3108c150480d, 0x31088160480d, 0x3008c160480d, 0x3108c180480d, 0x31090160480d, 0x3208c160480d, 0x3108c1d04809, 0x310bc1d0480d, 0x3b08c1d0480d, 0x3108c1e0580d, 0x31094160480d, 0x3308c160480d, 0x310a0160480a, 0x2608c160480d, 0x310a8230580d, 0x3108c1a0480d, 0x3408c160480d, 0x3508c160480c, 0x31084160480d, 0x370c4230580d, 0x3108c1b0480d, 0x3109c160480d, 0x3108c0d02c08, 0x310bc160340b, 0x3b08c160340b, 0x310580d02c05, 0x230580d02c02, 0x3108c1f0380d, 0x3108c1c05812, 0x310a4160480d, 0x3608c160480d, 0x310bc120380d, 0x3b08c120380d, 0x310ac1603c0d, 0x3808c160440d, 0x310480d02006, 0x230480d02007, 0x310480d02005, 0x230480d02002, 0x310581203406, 0x230581203407, 0x310bc1203408, 0x3b08c1203408, 0xec2f0480d, 0x3b0bc160480d, 0x3b0c42f0480d, 0x310581203404, 0x2f0581203402, 0x310bc130480d, 0x3b0bc230480d, 0x3908c160480d, 0x3b0581203405, 0x230581203401, 0x3b08c140480d, 0x310b4160480d, 0x31064160480d, 0x160480d01402, 0x3c080160480d, 0x310b0230480d, 0x2305c160480d],
  [0x3108c160480d, 0xc423058120340d, 0x3108c1604810, 0xc423058120400d, 0xf43108c160480d, 0xc4230581203403, 0xc423074160480d, 0xc4230581203409, 0xc42808c160480d, 0xc423058120340a, 0xd43108c160480d, 0xc423058120340c, 0xc423058120480d, 0x3108c160340b, 0xc423058120340b, 0xc42307c160480d, 0xc423058120380d, 0xc42b08c160480d, 0xc4230581203c0d, 0xe03108c160480d, 0xc423058120440d, 0xc423058160480d, 0x3108c1203408, 0xc4230581203408, 0x310bc160480d, 0xc42f08c160480d, 0xc423058130480d, 0x3b08c160480d, 0xec3108c160480d, 0xc423058140480d, 0xc42308c160480d, 0x310581203405, 0xc4230581203405, 0xf03108c160480d, 0xc423080160480d, 0xc43108c160480d, 0x230581203402, 0xc4230581203402],
  [0x3108c160480d]]

def actT2 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0xc1800182000302000600, 0x602, 0xae75015cda02b99408d2501163a015c1802b8200570200ae00, 0xac1801582002b02005600, 0x19c40112900064e000c1800182000302000600, 0x19c801135000666000c1800182000302000600, 0x602, 0x541800a82001502002a00, 0x1141802282004502008a00, 0x1241802482004902009200, 0x841801082002102004200, 0x8c1801182002302004600, 0x602, 0x602, 0xc1800182000302000600, 0xc1800182000302000600, 0x19c801135000666000c1800182000302000600],
  [0x1a4800339000610000c1800182000302000600, 0x602, 0x602, 0x602, 0xd24001a4400048000675000ce402295805325000610000c1800182000302000600, 0xd2a001a48003390006710000e002495805525000610000c1800182000302000600, 0x602, 0x602, 0x0, 0x0, 0x1048000602, 0x1038000602, 0x0, 0x0, 0xae9d015d2a02ba340574280ae82015cd402e9880572900b64a01647402b8e40201c00ae10015c1802b8200570200ae00, 0x2a920054e400a94401524802a1000541800a82001502002a00, 0xd240019c800334800610000c1800182000302000600, 0xd24001a2400339000610000c1800182000302000600, 0x2549005272006c7400e8e40201c000e10001c1800382000702000e00, 0x95240149c805f1d004e10009c1801382002702004e00, 0x4d240209c80611d000e10001c1800382000702000e00, 0xad0401598802b2680564a00ac740318e40301c00561000ac1801582002b02005600, 0xcd220019d40673280d256014c9a0299280651c80a610014c180298200530200a600, 0xd2a015a140313880da5601549a02a92806b1c80aa1001541802a8200550200aa00, 0x1ba2803535002a550024740158e40301c001610002c1800582000b02001600, 0x6e92000ce402395806f2500421000841801082002102004200, 0x69200d4e402395807125001610002c1800582000b02001600, 0xe53c01ca480394100726500e4c401c9280391d00721000e41801c82003902007200, 0xd32001a4800348808090000ce40089a800333000610000c1800182000302000600, 0x34a80068a000cea00194800d25000610000c1800182000302000600, 0x34e800692000ce40019b800d31000610000c1800182000302000600, 0x34e800692000ce40019b800d31000610000c1800182000302000600, 0xf53a01ea1403d41007a7200f4c401e92803d1d007a1000f41801e82003d02007a00, 0xd34001a4801145000686000ce40019c405038000610000c1800182000302000600, 0x34e800676000cd400798800329000610000c1800182000302000600, 0x34f000692000d1c007a0800339000610000c1800182000302000600, 0x34f000692000d1c007a0800339000610000c1800182000302000600, 0x0, 0x6048000602, 0x6038000602, 0x0, 0x0, 0x551400a9a80152a802a5201cc7400a8e40701c002a1000541800a82001502002a00, 0x24a28047448120880114d40239a408034002a55004c7400a8e40701c002a1000541800a82001502002a00, 0x42920085220502400033900421000841801082002102004200, 0x692008ce40119c40b038004610008c1801182002302004600, 0x22a28023448160880114da0229a80452a808a52014c740228e40801c008a1001141802282004502008a00, 0x24a340494500926a0084d20501a00492a8092520154740248e40901c00921001241802482004902009200, 0x692000cda0019a80751d000610000c1800182000302000600, 0x68d000d140019c80771d000610000c1800182000302000600, 0x606, 0x606, 0x0, 0x0, 0x1a6800330800610000c1800182000302000600, 0x1a6800330800610000c1800182000302000600, 0x602, 0x602, 0xcee0019cc07f3780fe6b00d4ce01998c0812b81025300dc9e01892c07d1f80f63b000c1e0680380030680000c000c1606002800304800008000c0e03001807f02800004000c0600800807900800000, 0x34a800692000d220002400033a800672000ce20001c00852b00fe5200d49c0419280030800060c000c1400182000302000600, 0x1a740034d000699000130001a5805147006682000cec0019c80033700fe6a000ccc0079880030800060e000c1800182000302000600, 0xc04c000602, 0x602, 0xd24001a440e048000675000ce400195808725000610000c1800182000302000600, 0x1a740034a800691000cea0019c800338800070009cdc0189880032b010252000c9c0069280030800060c000c1400182000302000600, 0x692000ce40019c40e038000610000c1800182000302000600, 0x602, 0xd04c000602, 0xd2a001a480033900067103c0e000195808925000610000c1800182000302000600, 0x692000d2207824000339000610000c1800182000302000600, 0x60e, 0x0, 0x1a740034d000692004514001a18003390006710400e00019b800131000610000c1800182000302000600, 0x34d000692000d2208024001145000686000ce200894800327000610000c1800182000302000600, 0x60e],
  [0x34f80069b000d2e001a4c0504900068f004516001a1c00f41800677000ce60201c80033780226b000cce00698c0152b802653002c9e00492c0071f800a3b000c2603804800308800010000c1e0300380030680000c000c1601802800304800008000c0e01001801102800004000c0600800800100800000, 0x19610006ad003d5200ba6800342801a81002cca00498400726800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x160920280e40680480100801800e0040180480280100401000600400800180c00001002000, 0x1b080035a8006b1000d34001a340034480066d000cd20089540112880063e000c740018500030800060c000c1000081800302000600, 0xd9c002b34110660046ca000d8c002b14100620042c200557c002af40f05e0006ba00456c002ad40005a000ab200055c002ab400056000aaa001524002a2400539003e690014a200292401b1f003a3d0380780018580050a000a1000141800282000502000a00, 0x9584001ab400755000ea9050150014a6800342800e82009d0209820000332800e620094c209018001b29003a510380a0003934007250022490000900038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0xd8a019b040195d0012b905c170001a740314c802e9200bd220b02400033b0012750000e80049c80253700066a0004cc0049940003200126200b4a400493802b2682a04c0014720048500090800060e00241800482000902001200, 0x6ec2000d5a005aa800b548340a800d534001a1400b4100428106410000a9d8009350056690540d000599400b310006610000c000193400b250026490600900058f400b1d00023900007000585000b0800160c002c1000581000301001600, 0xd670006cd070198006b2400d60801aba000d3c006a740004e001a9a00852c018a480274700428a00050c006a1400042001a820034e401d9a800d3300726506c0c800685000309001a1000341800682000d02001a00, 0x3668006c2000d5a001aa80035483e0a8000d34001a5800d4500728906c110001a1400341000681000100001994003310006610780c0001934003250022490740900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x367001ecd000198007b2800363001ec5084188006b0800b5f0066ba001d6c011ac800157001ead000158007aa800f4d001e9200fd14007a1803d42840084003ce400185800f0a001e10003c1800782000f02001e00, 0x3670006c2000d7c007ac803d588400b0000d5a001aa8003548000a8000d34001a14003410006810901000019940033100066108c0c0001934003250022490880900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x13610006b5004562020a68003468022890054da0099a40112300224500008800890801120800040001c7c0028e80110a00221000441800181801102002200, 0x4e0920980e41480480200805000e0080181280280200401000600800800180c00001004000, 0x1b08003568006a9000d34001a1400340800665000cc20019340032480023d0004720018500030800060c000c1000181001101000600, 0xd8a009b040135d00069d010d32020a480033b0026750000e80099c80113700266d0000d80099a802533000662004cac00a9542a02a005a4a0014740098500130800060e004c1800982001302002600, 0x92c2011d821783000035a802ab2008d621682c00454d008e990b8130001a34015450042890b01100099c8015388540700054da00a9a8003348000680054cc00a954015290022510000a00018f80091d002a390ac07000a85001508002a0c00541000181801502002a00, 0x6cd004592008b1404d5d00069e00453a0002700114d004296010d24008a380114680008c004514025a18021410086720044dc0019b430036007662007c740088500030900221000441800882001102002200, 0xd92001b080035a8006b1000d34008a4800348860090000d1a001a2800344800088000d0c0019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0x6ce00459a000330011650006c6004584011af80135d0022b600456a0002d001159000eae008d54008a780134900228e000d1a18823003f410082720014740018580110a00221000441800882001102002200, 0xd94001b080115d0006b90c4170001ad4003590006b1000160001ab80034d00068d000d120019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0xd7a001ae80035c80a0b8000d2a001a4800348808090000cbc0019740002e00065a000cb20001600152b002652002c9c0049280030a000610000c1400182000302000600, 0x660860c80cc1a80480300806800e00c0181280280300401200600c00800180c00001006000, 0x6c20e4180001ab80035686e0ac000d52001a683804c000686000d0a1b021000340800665000cc20089340152480023d0054720018500030800060c000c1000181000301000600, 0x1a7c0034d800697000d261d82483c048874090000d1e020a2c00343801e83000cee0201d400339808072010cde0219ac04f338062630114ae17015804129806a4f005c960b01280291f800a3b000c261f004800308808010000c1e1e80380030680800c000c161c002800304808008000c0e13001804102808004000c0605000801700808000, 0x1b34003648006c5000d82001ae80035c8800b8000d3c001a740004e00069a000d320202600034b000695000128001a480274700868a013d0c018a080033b0006750fc0e80019c80033700866a000ccc0069880472b005e4a000c280018480030800060e000c1800182000302000600, 0x1b080035e8006ba000d722082e00034d0006990fc130001a54003490006910001200019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x1a7c0034d80069701412a001a4c0504900268f004d16005a1c03341800677000ce61d81c840038874070000cde0269ac00333801a630124ae17815801329806e4f0064960b81280251f800a3b000c262180480030880a010000c1e2100380030680a00c000c161c80280030480a008000c0e1380180130280a004000c060580080190080a000, 0x1b38003668000cc000d94001b24050640006c6000d84001af80035e8000bc000d74028ad8013590016ae00cd54001a780034d000696000d2a2202500034900068e004d14001a1800f41000672000ce21e01c00472b00124a000c2c00185000309000610000c1800182000302000600, 0x1b08003608880c0000d7a001ae80035c8000b8000d34001a54003490006911141200019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x6c5000d82001ae80033f00067d0000f80019e80033c800078000cec0019c80033700226a000ccc0069880030a00060e000c1800182000302000600, 0x8409a1180c22380480600806800e0180181400280600401800601800800180c0000100c000, 0x1b08003568006a9000d34001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600, 0x3670006cd000198001b28003630006c5000188001b080035f0006ba000d6c008ac800357001aaa000d3c001a744804e000692000d1c007a080033900066e0034c40018580030a000610000c1800182000302000600, 0xd94001b24480640006c5000d84001b04000600006ba004564001ab80034e80069a000d320002600034900228a000d0c0019d8003390006711240e00019b8011350006660004c40018500030800060e000c1800182000302000600, 0x6a6000d4a000290003510006a1000140001a780034d000696000d24001a3801145000686003d040019c800309000610000c1800182000302000600, 0x7c09a1280c22380480700806a00e01c0181480280700401a00601c00800180c0000100e000, 0x1b08003568006a9000d34001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600],
  [0x2204f84209b07412e0e024c1b04902808f04c11605821c0a0418340770640e60c01c81203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b0940261200482300880001008001e0f80381e00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT2 : List ℕ := [0x1804000190601d, 0x10000181d06418, 0x240003c230601a, 0x18000241d06819, 0x500f0001a06023, 0x10000301d06818, 0x24000301d06418, 0x3c000481d06418, 0x18000101d06019, 0x200003c230601a, 0x10000502306818, 0x480f0001a06023, 0x3c0c0001a06023, 0x240003c2306c1a, 0x10040241a06018, 0x3c00024230601b, 0x10000301d06418, 0x10000481d06418, 0x200003c2306c1a, 0x18000241d06019, 0x180003c2306c1a, 0x301a06018, 0x3c090001b06823, 0x50090001b06023, 0x24000181d06418, 0x3c000181d06418, 0x10000181d06818, 0x10000181d06c18, 0x24000001806018, 0x30000241d06019, 0x3c000001806018, 0x480003c1d06019, 0x180003c230601a, 0x3800024230601b, 0x10000482306418, 0x10000502306418, 0x10000302306418, 0x180003c1d06c19, 0x1800024230601b, 0x10000481d06c18, 0x180003c1d06019, 0x480f0001906023, 0x30090001906023, 0x241a06018, 0x241a06419, 0x24090241a06018, 0x3c0f0241a06818, 0x240003c2306c18, 0x3c000242306818, 0x10040301a06818, 0x240003c2306019, 0x481b06018, 0x180003c2306c19, 0x3c000242306019, 0x18000242306819, 0x500f0001906023, 0x50090001906023, 0x582308c18, 0x301d07418, 0x481d07418, 0x3c060001a0601d, 0x240003c1d0601a, 0x180003c1d06c1a, 0x180003c1d0601a, 0x18000241d0601b, 0x3c060001a06023, 0x10000182306418, 0x241d07418, 0x3c1d07418, 0x24060241a06018, 0x18060241a06818]

def S2 (s i : ℕ) : List ℕ := unpackW wdT2 9 ((levT2.getD s []).getD i 0)

def N2 (s : ℕ) : ℕ := (levT2.getD s []).length

def A2 (s i tag : ℕ) : ℕ := findAct 4096 ((actT2.getD s []).getD i 0) tag

def W2 (w : ℕ) : ℕ := witT2.getD w 0

def Z2 (s : ℕ) := barrier 24 S2 N2 A2 W2 idRot s

theorem enc_inputs2 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT2) = xsT2 := by decide +kernel

theorem enc_goal2 : encL fT2 rowsT2 = goal 24 := by decide +kernel

theorem mask2 : mask 24 = 2 ^ rowsT2.length - 1 := by decide +kernel

theorem proper_fail2 : ∀ zs ∈ xsT2.sublists, zs ≠ xsT2 → (cov 24 zs &&& lo 24) ≠ lo 24 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked2 : ∀ s ≤ 7, ∀ i < N2 s, Z2 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun2 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 24) (goal 24) s xsT2) : False := by
  have hc : NatRun (mask 24) (goal 24) 7 xsT2 := extend_run h hs
  have p : xsT2.Perm (S2 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked2 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub2 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT2 → NatRun (mask 24) (goal 24) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT2
  · subst e; exact noRun2 s hs h
  · exact proper_fail2 zs (List.mem_sublists.2 hz) e (required h)

theorem low2 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT2 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT2 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 24) (encL fT2 rowsT2) s' (ws.map fun a => encL a rowsT2) :=
    Run.map (fun a : BFn 5 => encL a rowsT2)
      (fun a => by rw [mask2]; exact encL_inv a rowsT2)
      (fun a b => encL_and a b rowsT2) (fun a b => encL_or a b rowsT2) hrun
  rw [enc_goal2] at hr
  refine no_sub2 s' (by omega) _ ?_ hr
  rw [← enc_inputs2]
  exact hsub.map _

def mono2 : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [10, 11]⟩]

theorem mono_ok2 : ∀ g ∈ mono2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono2, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval2 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono2, 12⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve2 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono2, 12, mono_ok2, ?_, mono_eval2⟩
  by_contra hlt
  have hlen : mono2.length = 8 := rfl
  apply low2
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT3 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 9, 9, 9, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 3, 5, 17, 3, 6, 10, 5, 6, 10, 11, 13, 25, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT3 : List ℕ := [0x54de4f000e07, 0xaba3b9038038, 0xcd34d2cc30c0, 0xf23f20f03f00, 0xffc804ffc000]

abbrev fT3 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT3 : List ℕ := [0x54de4f000e07, 0xaba3b9038038, 0xcd34d2cc30c0, 0xf23f20f03f00, 0xffc804ffc000]

def levT3 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x50100300801]]

def actT3 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0xa48005450002860004e40009b80033100021000041800082000102000200]]

def witT3 : List ℕ := [0xc000181c06418, 0x1803000190601c, 0x180000c1c06019]

def S3 (s i : ℕ) : List ℕ := unpackW wdT3 9 ((levT3.getD s []).getD i 0)

def N3 (s : ℕ) : ℕ := (levT3.getD s []).length

def A3 (s i tag : ℕ) : ℕ := findAct 4096 ((actT3.getD s []).getD i 0) tag

def W3 (w : ℕ) : ℕ := witT3.getD w 0

def Z3 (s : ℕ) := barrier 24 S3 N3 A3 W3 idRot s

theorem enc_inputs3 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT3) = xsT3 := by decide +kernel

theorem enc_goal3 : encL fT3 rowsT3 = goal 24 := by decide +kernel

theorem mask3 : mask 24 = 2 ^ rowsT3.length - 1 := by decide +kernel

theorem proper_fail3 : ∀ zs ∈ xsT3.sublists, zs ≠ xsT3 → (cov 24 zs &&& lo 24) ≠ lo 24 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked3 : ∀ s ≤ 5, ∀ i < N3 s, Z3 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun3 (s : ℕ) (hs : s ≤ 5) (h : NatRun (mask 24) (goal 24) s xsT3) : False := by
  have hc : NatRun (mask 24) (goal 24) 5 xsT3 := extend_run h hs
  have p : xsT3.Perm (S3 5 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked3 5 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub3 : ∀ s ≤ 5, ∀ zs : List ℕ, zs.Sublist xsT3 → NatRun (mask 24) (goal 24) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT3
  · subst e; exact noRun3 s hs h
  · exact proper_fail3 zs (List.mem_sublists.2 hz) e (required h)

theorem low3 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT3 5 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT3 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 5 h
  have hr : NatRun (mask 24) (encL fT3 rowsT3) s' (ws.map fun a => encL a rowsT3) :=
    Run.map (fun a : BFn 5 => encL a rowsT3)
      (fun a => by rw [mask3]; exact encL_inv a rowsT3)
      (fun a b => encL_and a b rowsT3) (fun a b => encL_or a b rowsT3) hrun
  rw [enc_goal3] at hr
  refine no_sub3 s' (by omega) _ ?_ hr
  rw [← enc_inputs3]
  exact hsub.map _

def mono3 : List Gate := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [8, 9]⟩]

theorem mono_ok3 : ∀ g ∈ mono3, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono3, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono3, 10⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve3 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono3, 10, mono_ok3, ?_, mono_eval3⟩
  by_contra hlt
  have hlen : mono3.length = 6 := rfl
  apply low3
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 5
    omega

def rowsT4 : List ℕ := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 8, 8, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 5, 9, 17, 6, 10, 7, 11, 19, 5, 6, 9, 10, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT4 : List ℕ := [0x54d5e70000e7, 0xabaaf80380f8, 0xcd3329cc3300, 0xf23c52f03c00, 0xffc084ffc000]

abbrev fT4 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT4 : List ℕ := [0x54d5e70000e7, 0xabaaf80380f8, 0xcd3329cc3300, 0xf23c52f03c00, 0xffc084ffc000]

def levT4 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x50100300801]]

def actT4 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x270]]

def witT4 : List ℕ := [0x200003c1b06818]

def S4 (s i : ℕ) : List ℕ := unpackW wdT4 9 ((levT4.getD s []).getD i 0)

def N4 (s : ℕ) : ℕ := (levT4.getD s []).length

def A4 (s i tag : ℕ) : ℕ := findAct 4096 ((actT4.getD s []).getD i 0) tag

def W4 (w : ℕ) : ℕ := witT4.getD w 0

def Z4 (s : ℕ) := barrier 24 S4 N4 A4 W4 idRot s

theorem enc_inputs4 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT4) = xsT4 := by decide +kernel

theorem enc_goal4 : encL fT4 rowsT4 = goal 24 := by decide +kernel

theorem mask4 : mask 24 = 2 ^ rowsT4.length - 1 := by decide +kernel

theorem proper_fail4 : ∀ zs ∈ xsT4.sublists, zs ≠ xsT4 → (cov 24 zs &&& lo 24) ≠ lo 24 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked4 : ∀ s ≤ 4, ∀ i < N4 s, Z4 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun4 (s : ℕ) (hs : s ≤ 4) (h : NatRun (mask 24) (goal 24) s xsT4) : False := by
  have hc : NatRun (mask 24) (goal 24) 4 xsT4 := extend_run h hs
  have p : xsT4.Perm (S4 4 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked4 4 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub4 : ∀ s ≤ 4, ∀ zs : List ℕ, zs.Sublist xsT4 → NatRun (mask 24) (goal 24) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT4
  · subst e; exact noRun4 s hs h
  · exact proper_fail4 zs (List.mem_sublists.2 hz) e (required h)

theorem low4 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT4 4 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT4 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 4 h
  have hr : NatRun (mask 24) (encL fT4 rowsT4) s' (ws.map fun a => encL a rowsT4) :=
    Run.map (fun a : BFn 5 => encL a rowsT4)
      (fun a => by rw [mask4]; exact encL_inv a rowsT4)
      (fun a b => encL_and a b rowsT4) (fun a b => encL_or a b rowsT4) hrun
  rw [enc_goal4] at hr
  refine no_sub4 s' (by omega) _ ?_ hr
  rw [← enc_inputs4]
  exact hsub.map _

def mono4 : List Gate := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [7, 8]⟩]

theorem mono_ok4 : ∀ g ∈ mono4, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono4, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval4 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono4, 9⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve4 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono4, 9, mono_ok4, ?_, mono_eval4⟩
  by_contra hlt
  have hlen : mono4.length = 5 := rfl
  apply low4
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 4
    omega

def rowsT5 : List ℕ := [1, 1, 1, 2, 2, 4, 4, 8, 10, 10, 10, 12, 12, 12, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 5, 9, 3, 6, 5, 6, 9, 11, 14, 26, 13, 14, 28, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT5 : List ℕ := [0x24f26bc01c007, 0x4b95d640e0718, 0x9d2e9c8703860, 0xf24fe13803f80, 0xfff9003ffc000]

abbrev fT5 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT5 : List ℕ := [0x4940003ff8, 0x6e10003f80, 0x6ffc003fff, 0x90424000000, 0x422088000000, 0x904940000000, 0xdb01ec7fc07f, 0xdb49ec7fffff, 0xdb6ffc7fffff, 0x2042610000000, 0x24f000001c000, 0x24f26bc01c007, 0x24f6ffc01ffff, 0x2df6ffc01c007, 0x4205c00000700, 0x4b910000e0000, 0x4b95d640e0718, 0x4fb7dec0e0718, 0x62d16378fc79f, 0x6bd7f740e0718, 0x6ff7ffc0fc71f, 0x900e800003800, 0x9d28000700000, 0x9d2e9c8703860, 0x9dbedec703860, 0xb46a29bf1f8e7, 0xbd6efd8703860, 0xbdfeffc71f867, 0xdb09003fe0000, 0xdb0d943fe3ff8, 0xdfb90007e0000, 0xdfbfdec7e3f78, 0xf249003800000, 0xf24b613800000, 0xf24fe13803f80, 0xf2dfe37803f80, 0xf66fe9b803f80, 0xf6f900381c000, 0xf6fb6bf81c007, 0xf6ffebf81ff87, 0xfb4ff53803f80, 0xfbd90038e0000, 0xfbdff778e3f98, 0xff69003f00000, 0xff6ffdbf03fe0, 0xfff9003ffc000, 0xfff91efffc07f, 0xfff9427ffc000, 0xfffb08bffc000, 0xfffb613ffc000, 0xfffb6bfffc007, 0xfffd943ffc000, 0xfffdd67ffc718, 0xffff9cbfff860, 0xffffe13ffff80]

def levT5 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x2706014, 0x2706c11],
  [0x88180440c, 0x881e06011, 0xb82306415, 0xb82307012, 0x84180500c, 0x841b0440c, 0x9c180440a, 0x881a0600c, 0x88130440c, 0x601103008, 0xb8230800e],
  [0x2e08c180440c, 0x2e08c1e06011, 0x3308c180440c, 0x2e08c1a0600c, 0x2e08c130440c, 0x2e0601103007, 0x23084180440c, 0x230601103003, 0x2e08c1e06818, 0x2e08c1e04c11, 0x230781d06011, 0x2e0781804407, 0x230841e06011, 0x230781804403, 0x3308c1e06011, 0x23074180440c, 0x2e08c1805404, 0x2e08c190440c, 0x2e090180440c, 0x3008c180440c, 0x2e08c1c04405, 0x2e08c180480c, 0x2e094180440c, 0x3108c180440c, 0x2e0a0180440a, 0x2608c180440c, 0x2e08c180500c, 0x2e08c1b0440c, 0x3208c180440c, 0x21060110300a, 0x3308c1a0600c, 0x3308c130440c, 0x330601103007, 0x88180440c, 0x23088180440c, 0x33088180440c, 0x230601103001, 0x3308c180440b, 0x2e088180440c, 0x2e08c1a04c0c, 0x2e0681803007, 0x230841a0600c, 0x230681803003, 0x2e08c2003006, 0x2307c180440c, 0x8c21080180440c, 0x2e08c180440e, 0x2e0a4180440c, 0x3408c180440c, 0x2e0ac1803c0c, 0x2b084180440c, 0x2a08c180440c, 0x3508c180400c, 0x2e04c1103007, 0x23084130440c, 0x2304c1103003, 0x2e0b4160440c, 0x2d084180440c, 0x2c08c180440c, 0x3608c170440c, 0x2f0601103007, 0x180440c01c03, 0x2f08c180440c, 0x210601103007, 0x37084180440c, 0x2708c180440c, 0x230601103009, 0x23060110340c, 0x230601103002],
  [0x2e08c180440c, 0xb823060110300c, 0x2e08c1e06011, 0xb823078180440c, 0xb823060150440c, 0xb8230601103004, 0xb823070180440c, 0xb8230601103005, 0xb82808c180440c, 0xb823060110300a, 0x3308c180440c, 0xcc2e08c180440c, 0xb823060110300b, 0xb823060110440c, 0x2e08c1a0600c, 0xb823068180440c, 0xb823080180440c, 0xb8230601103006, 0xb82b08c180440c, 0xb8230601103c0c, 0xd42e08c180440c, 0xb823060110400c, 0xb823060180440c, 0x2e08c130440c, 0xb823060130440c, 0xb82d08c180440c, 0xb823060160440c, 0xd82e08c180440c, 0xb823060170440c, 0xb82308c180440c, 0x2e0601103007, 0xb8230601103007, 0xdc2e08c180440c, 0x23084180440c, 0xb823084180440c, 0xb82e08c180440c, 0x230601103003, 0xb8230601103003],
  [0x2e08c180440c]]

def actT5 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x182000302000600, 0x182000302000600],
  [0xc1800182000302000600, 0x60a, 0xba7601741802e82005d0200ba00, 0x627600c41801882003102006200, 0x98800330800060000c1800182000302000600, 0x98800330802060000c1800182000302000600, 0xcca001988003250006490040900018e80111c800038000c1800182000302000600, 0x60a, 0x60a, 0x602, 0xa9d801337007e6200541800a82001502002a00],
  [0x1a7800f41000610000c1800182000302000600, 0x60a, 0x34f001e9d000138007a1400f41001e10003c1800782000f02001e00, 0x60a, 0x60a, 0x602, 0x1a740034d000692004514001a1800131000610000c1800182000302000600, 0x602, 0x0, 0x0, 0x60e, 0x0, 0x60a, 0x0, 0x104e001e0a, 0x1a7400f31000610000c1800182000302000600, 0xba9e018d0403098805f2500ba4900809002e8f405d1d00ba1001741802e82005d0200ba00, 0x74f005a8200647400d8e40201c000e10001c1800382000702000e00, 0xa53c016a080191d00521000a41801482002902005200, 0x1a7800f4100561000ac1801582002b02005600, 0x629e00c5040189880312680624a00c4740328e40301c00621000c41801882003102006200, 0xb4f007e8200bc9401892403024001610002c1800582000b02001600, 0x853c01fa0802f2500421000841801082002102004200, 0x1a7800f41001610002c1800582000b02001600, 0x20a78041410082650104c40209280411d00821001041802082004102008200, 0x34f000282000ce40089a800333000610000c1800182000302000600, 0x34f00069d010138007a0800d31000610000c1800182000302000600, 0x34f00069d014138007a0800d31000610000c1800182000302000600, 0x69e000d3a00027000f41000610000c1800182000302000600, 0xa280034480c088000d04001a0400040000662000cc2028180003250022490100900018f40031d000610000c1800182000302000600, 0x704e001e0a, 0x804e001e0a, 0x1e02, 0xcee0019cc0033780226b000cce00098c0152b80d65300549e03492c0351f80ce3b000c1e0480380030680000c000c1604002800304800008000c0e03801801102800004000c0600800800100800000, 0x69e000d3a0002700034d000696000d24001a380114500068600350400098800309000610000c1800182000302000600, 0x34f001e9d000138007a680234b007692016d1c011a2800143001e85000108007a0800309001e10003c1800782000f02001e00, 0x1e02, 0x12d3a025a1404b41009610012c1802582004b02009600, 0x34f00069a000d2c001a4800347002e8a000d0c007a0800309000610000c1800182000302000600, 0x0, 0x0, 0x60a, 0x0, 0xaa780134b007e8a00550400a98801526802a4a0054740198e40a01c002a1000541800a82001502002a00, 0x1a7400f31000610000c1800182000302000600, 0x9ec0000d380019d000336002a54, 0x154f007e820144a400a9440a028002a1000541800a82001502002a00, 0x10a7803f4100421000841801082002102004200, 0x1a7800f41004610008c1801182002302004600, 0x34f00da82000cda0019a806d1d000610000c1800182000302000600, 0x229d004534027a480114680228a013d0c00f98801f1d00221000441800882001102002200, 0xd3c01fa0800339000610000c1800182000302000600, 0x2ca340594500b21001641802c8200590200b200, 0x0, 0x60a, 0x0, 0x34f00de82000cea0019c806f25000610000c1800182000302000600, 0x69d000d34001a5400349009e8a013d0c01b98803725000610000c1800182000302000600, 0xd3c016a0801135000610000c1800182000302000600, 0x1a5400349000610000c1800182000302000600, 0x602, 0x0, 0x1a7800341000610000c1800182000302000600, 0x602, 0x34e80069a000d2402ba2800343000610000c1800182000302000600, 0x69e00053a0002700014280028200dce400f9a8001330006650180c80399240711c80021000041800082000102000200, 0x602, 0x606, 0x602],
  [0x34f80c09e000d36001a5c0034980068f005d16001a1c00f41804082000cee0019cc0033780226b000cce00698c0152b802653002c9e00492c0071f800a3b000c2603804800308800010000c1e0280380030680000c000c1602002800304800008000c0e01801801102800004000c0600800800100800000, 0xb38003568002aa003d520102a000342801a81002cca00498400726800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x1809e02812c0680480100801600e00401800182c0000500200802400c00801008001002000, 0x3670006c6000d8a07831000360801eaa038150001a740034c800676000ce40089b801135000666000cc40018500030800020e000c1800182000302000600, 0x4ace000d7a011ae401d5500069500852200fa240153a8006710014d20029840112b000a550000a800294800127000a4d0000980029280191f00363d04007800285000508000a0c000c1400282000502000a00, 0x1d9c016ac800356800eaa00ad520982a000342800e8200a50209020000332800e62009cc2088180019290036510400a0003934007250022490000900038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0x7ace000d8a01db040335500069d00e53201ba440033b0012750000e80049c80353700066a0004cc004994000320012620024a40179380312682804c0014720048500090800060e00241800482000902001200, 0x2d9c01fac8003568016aa002d520b82a0003428016820085020b020002f350062690500d000599400b310006610000c000193400b250026490540900058f400b1d00023900007000585000b0800160c002c1000581000301001600, 0xd670006cd064198006b2400d630002aa000d3c006a740004e001a9a00852c01ca480294700428a00050c006a1400042001a820034e40219a800d330082650600c800685000309001a1000341800682000d02001a00, 0x3670006cd074198007ac8003568006aa000d520e02a000d45008289060110001a14003410006810001000019940033100066106c0c0001934003250022490680900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1e9f08813c1182742104e001e9b003d2e007a4c04547801e8b00050e01021400f41804082003cee0079cc00f37808a6b003cce00098c03f2b808e5300fc9e01992c02d1f803a3b01242612004800f08804010003c1e10003800f0680400c003c160f802800f04804008003c0e0f001804502804004003c0607000800100804000, 0xd9c007b3400066001eca003d9201032000363001ec5098188006b0800b5f0076ba001d6c011ac800157001ead000158007aa800f4f001e9a003d2c007a4800f47009a8a003d0c025a1425042001e82000c2c00785000109001e10003c1800782000f02001e00, 0x6ce003d64025ac4250580006ad000d54001aa400054000685000d020019940033080064d0044920018f40031d0002390000700018500030800060c000c1000181000301000600, 0x11670006b5005d62022aa8003468022890054da0099a40112300224500008800890801120800040001c7c0028e80110a00221000441800181801102002200, 0x5209e0781041500480300805000e00c01800182c0000500600809c00c01801008001006000, 0x1b38003628006c1003d54001a740034c800676000ce40019b80033500026600d4c40018500030800220e000c1800182000302000600, 0x2d0670026c6000d8a16031005360808eaa000d3a027a640033b0026750000e80099c80113700266d0000d80099a804f330006620144ac00a9542b02a00124a0014740098500130800060e004c1800982001302002600, 0x559c01fac800356802aaa008d521802a000342802a8200850217820005139002a710ac0e000a994015310006610000c000a934015250022490000900018f40151d0066390b807000a85001508002a0c00541000a81000301002a00, 0x22ce000d9a198330057648022c600458a1903100455500069e00453a0002700114d004296013d24008a380114680008c004514027a180214100aa720044dc0019b431036008662007c740088500030900221000441800882001102002200, 0x3670006b5000d62007aa8011490006910c4120001a34003450006890001100019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0x1b38017668000cc005d94001b18057610046be014d74008ad80175a8000b4005d64003ab802355002e9e005d2400ba380594686808c0135040018580170a002e10005c1800b82001702002e00, 0x1b3800363002eba0165721a02e00035a8006b2000d620002c000f5500068d000d120019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0x3670006bd000d72007aa80034a800691000cbc0019740002e00065a000cb20001600152b002652002c9c0049280030a000610000c1400182000302000600, 0x6c09e07c1041b80480400806a00e01001800182c0000500800809c00c02001009001008000, 0x1b380035e8006b9003d54001a5400348800675000ce20089580152900024e0054940018500030800060c000c1400182000302000600, 0x6ce000d9a1d0330003648006c6000d8a1c831000f5500069e000d3a0002700034d000696000d2a0002500034900528e013d14027a1803941000676000cea1c01d005535001a6200dc9400185000309000610000c1800182000302000600, 0x3670006bd000d72007aa80034d0006990e0130001a54003490006910001200019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x1b38003668000cc000d94001b18003610006be000d7a0002f00035d00b6b6014d64005ab803b5500069e000d2c001a543b04a002e8a003d040018580030a000610000c1800182000302000600, 0x1b38003610006c10ec180001af40035d0006b9000170001ad800f55000695000d220019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x1b180036280c0c4000d82007aa80033f00067d0000f80019e80033c800078000cec0019c80033700226a000ccc0069880030a00060e000c1800182000302000600, 0x4008a0f01041e80480500806a00e0140181400280500401600601400800180c0000100a000, 0x36707e0cc003d64001ab4003550006a90f8150001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600, 0x6ce000d9a000330003650006c6000d8a000310003610006be000d74001ad8057590006ae003554001a780034e88009c003d040018580030a000610000c1800182000302000600, 0x34f80c09d000d360302680034b8006930e4124001a3c0114586408a000d0e0e821800d41800677000ce60019bc011358006670004c62081880152b85a053002c9e01e92c0071f804a3b000c261f80480030880c010000c1e2100380030680c00c000c161b00280030480c008000c0e1480180110280c004000c060600080010080c000, 0x6ce000d94001b24400640006c6000d8a030310003610006c1000180001af80035d0006b6005d64001ab800f5500069d000d34001a640004c000692004514001a180033b000672000cdc0089a800333000262000c2c0018500030800060e000c1800182000302000600, 0xd4c001a94000520006a2000d420002800034f00069a000d2c001a4800347002e8a000d0c007a0800309000610000c1800182000302000600, 0x8808510c0721e80480700806e00e01c0181500280700401a00601c00800180c0000100e000, 0x1b38001590006ad000d52001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600],
  [0x2204f84209e0801360e025c1b04982a08f05011606021c0b0418140820680ee0c81cc1303782406b0240ce04018c1102b82005301c09e03012c0501f80803b0940261200482300880001007c01e0f00381d00680000c0600160b80281600480000803c00e0700180d00280000400c00601000801000800000]]

def witT5 : List ℕ := [0x14030001b0681e, 0xc000141e06c1a, 0x2000044240681c, 0x14000201e0701b, 0x2c000502706c1c, 0xc0002c1e0701a, 0x200002c1e06c1a, 0x44000501e06c1a, 0x140000c1e0681b, 0x1c00044240681c, 0xc0005c240701a, 0x38030501e06c1a, 0x140005c270901e, 0xc030201c0681a, 0x5c140001c06c27, 0x2c0305c270901e, 0xc0002c1e06c1a, 0xc000501e06c1a, 0x5c0b0202407827, 0x1c000502706c1c, 0x14000201e0681b, 0x440e0141e06c1a, 0x500005c270701b, 0xc0005c270901e, 0x2c1c0681a, 0x5c110001c06824, 0x140005c270701b, 0x200505c270901e, 0x20000141e06c1a, 0x44000141e06c1a, 0x5c0802c2707824, 0x440005c240701a, 0x20000001a0681a, 0x2c000201e0681b, 0x50000441e0681b, 0x5c00044240681c, 0x44000502c06c1a, 0x44000001a0681a, 0x440e0501e06c1a, 0x140305c270901e, 0xc0005c270701b, 0x38030141e06c1a, 0x2c0805c270901e, 0x380302c1e06c1a, 0x38000001a0681a, 0x14000441e0681b, 0x201c0681a, 0x201c06c1b, 0x20080201c0681a, 0x380e0201c0701a, 0xc0302c1c0701a, 0x5c050001c06c27, 0x5c030001c06824, 0x5c0000c240681c, 0x2c1e0781a, 0x201e0781a, 0x5c0b00c1e06827, 0x5c080141e06c24]

def S5 (s i : ℕ) : List ℕ := unpackW wdT5 9 ((levT5.getD s []).getD i 0)

def N5 (s : ℕ) : ℕ := (levT5.getD s []).length

def A5 (s i tag : ℕ) : ℕ := findAct 4096 ((actT5.getD s []).getD i 0) tag

def W5 (w : ℕ) : ℕ := witT5.getD w 0

def Z5 (s : ℕ) := barrier 26 S5 N5 A5 W5 idRot s

theorem enc_inputs5 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT5) = xsT5 := by decide +kernel

theorem enc_goal5 : encL fT5 rowsT5 = goal 26 := by decide +kernel

theorem mask5 : mask 26 = 2 ^ rowsT5.length - 1 := by decide +kernel

theorem proper_fail5 : ∀ zs ∈ xsT5.sublists, zs ≠ xsT5 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked5 : ∀ s ≤ 7, ∀ i < N5 s, Z5 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun5 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 26) (goal 26) s xsT5) : False := by
  have hc : NatRun (mask 26) (goal 26) 7 xsT5 := extend_run h hs
  have p : xsT5.Perm (S5 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked5 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub5 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT5 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT5
  · subst e; exact noRun5 s hs h
  · exact proper_fail5 zs (List.mem_sublists.2 hz) e (required h)

theorem low5 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT5 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT5 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 26) (encL fT5 rowsT5) s' (ws.map fun a => encL a rowsT5) :=
    Run.map (fun a : BFn 5 => encL a rowsT5)
      (fun a => by rw [mask5]; exact encL_inv a rowsT5)
      (fun a b => encL_and a b rowsT5) (fun a b => encL_or a b rowsT5) hrun
  rw [enc_goal5] at hr
  refine no_sub5 s' (by omega) _ ?_ hr
  rw [← enc_inputs5]
  exact hsub.map _

def mono5 : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [10, 11]⟩]

theorem mono_ok5 : ∀ g ∈ mono5, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono5, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval5 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono5, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve5 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfee8eae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono5, 12, mono_ok5, ?_, mono_eval5⟩
  by_contra hlt
  have hlen : mono5.length = 8 := rfl
  apply low5
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT6 : List ℕ := [1, 1, 2, 2, 3, 3, 3, 4, 4, 8, 8, 12, 12, 12, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 5, 9, 6, 10, 7, 11, 19, 5, 6, 9, 10, 13, 14, 28, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT6 : List ℕ := [0x24f2bcc01c073, 0x4b955f00e007c, 0x9d2e654703980, 0xf24f8ab803e00, 0xfff8103ffc000]

abbrev fT6 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT6 : List ℕ := [0x7efc003fff, 0x901c0000070, 0x422244000000, 0x904450000000, 0xdb07547fc1ff, 0x2042888000000, 0x24f010001c000, 0x24f2bcc01c073, 0x2df6fdc01c073, 0x42050a0000000, 0x4b901000e0000, 0x4b955f00e007c, 0x4fb77f40e007c, 0x62d19ab8fc67f, 0x66f7bec01c073, 0x6bd7df80e007c, 0x6ff7ffc0fc07f, 0x900e000003800, 0x9d28000700000, 0x9d2e654703980, 0xb46aa0ff1ff83, 0xbd6eedc703980, 0xbdf810071c000, 0xbdfefdc71f9f3, 0xdb0d433fe3f8c, 0xdf2f6f4703980, 0xdfb81007e0000, 0xdfbf7f47e39fc, 0xf248003800000, 0xf24f8ab803e00, 0xf66faef803e00, 0xf6f810381c000, 0xf6ffbef81fe73, 0xfb4fcfb803e00, 0xfbd81038e0000, 0xfbdfdfb8e3e7c, 0xff6fefff03f80, 0xfff8103ffc000, 0xfffa347ffc000, 0xfffa98bffc000, 0xfffabcfffc073, 0xfffc553ffc000, 0xfffd1a3ffc000, 0xfffd5f3ffc07c, 0xfffe757fff980, 0xffff9abfffe00]

def levT6 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x260781403008, 0x26078190500c, 0x260781505008, 0x260780e03008, 0x260500c02005, 0x1e0500c02001, 0x260781905414, 0x26078190380c, 0x260641403005, 0x1e0641403001, 0x260781404402, 0x260781803003, 0x1e05c1403008, 0x260781403408, 0x2607c1403008, 0x270781403008, 0x260841403006, 0x200781403008, 0x260781404008, 0x260781603008, 0x280781403008, 0x290781403007, 0x260781503808, 0x260541402005, 0x1e0541402001, 0x260781c02004, 0x1e06c1403008, 0x260781403009, 0x260881403008, 0x2a0781403008, 0x260901402808, 0x230781403008, 0x260781403c0c, 0x260781a03008, 0x2b0781403008, 0x2c0781402c08, 0x260380c02005, 0x1e0380c02001, 0x260941203008, 0x2d0781303008, 0x140300801401, 0x2e0741403008],
  [0x260781403008, 0x981e0500c02008, 0x26078190500c, 0x981e0641403008, 0x981e0501103008, 0x981e0500c02002, 0x981e0601403008, 0x981e0500c02003, 0x98210781403008, 0x981e0500c02006, 0xa4260781403008, 0x981e0500c02007, 0x981e0500c03008, 0x260781505008, 0x981e0541403008, 0x981e0701403008, 0x981e0500c02004, 0x98240781403008, 0x981e0500c02808, 0xb0260781403008, 0x981e0500c02c08, 0x981e0501403008, 0x260780e03008, 0x981e0500e03008, 0x98250781403008, 0x981e0501203008, 0xb4260781403008, 0x981e0501303008, 0x981e0781403008, 0x260500c02005, 0x981e0500c02005, 0xb8260781403008, 0x981e0741403008, 0x98260781403008, 0x1e0500c02001, 0x981e0500c02001],
  [0x260781403008]]

def actT6 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x610000c1800182000302000600, 0x60a, 0x60a, 0x60a, 0x602, 0x602, 0x0, 0x0, 0x0, 0x0, 0x742800e610084920038f40071d000e10001c1800382000702000e00, 0x11a580534100a262008c9a01192804f1d004610008c1801182002302004600, 0xa440211c80421000841801082002102004200, 0x5524801610002c1800582000b02001600, 0x2325001610002c1800582000b02001600, 0x561000ac1801582002b02005600, 0x17a7802f41005e6500bcc401792802f1d005e1000bc1801782002f02005e00, 0x2b9c80071c800e10001c1800382000702000e00, 0x2f30800610000c1800182000302000600, 0x2d31000610000c1800182000302000600, 0x610000c1800182000302000600, 0xdd1401ba1403741006e1000dc1801b82003702006e00, 0x0, 0x0, 0x0, 0x1ca580394100726200e49a01c9280391d00721000e41801c82003902007200, 0x1a440591d000610000c1800182000302000600, 0x3b28800e10001c1800382000702000e00, 0x3929000e10001c1800382000702000e00, 0x610000c1800182000302000600, 0x1fa7803f45007e6d00fcd401f94803f1c807e1000fc1801f82003f02007e00, 0x229c80191d000610000c1800182000302000600, 0x4130800610000c1800182000302000600, 0x3f35000610000c1800182000302000600, 0x610000c1800182000302000600, 0xd1a001a2800f41000610000c1800182000302000600, 0x0, 0x0, 0x34a800675000ce400194800125000610000c1800182000302000600, 0x11d34023a5404749008e10011c1802382004702008e00, 0x0, 0x1253a024a6805b4900921001241802482004902009200],
  [0xd3e001a6c0034b802a93000d1e001a2c00743801e83000cee0099cc0033780066b000cce00698c0072b802253002c9e00492c0071f800a3b005c2602804800308800010000c1e0200380030680000c000c1601802800b04800008000c0e01001800302800004000c0600800800100800000, 0x1d5a007aa400342801a81002cca00498400726800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x480480100801000e00401800182c0000500200801c00c00801006001002000, 0x6c5000d82001a740034c801676002ce40019b800335000666000cc40018500030800020e000c1800182000302000600, 0x35e801eb900656a003ab40034a803e91007512006a0400b3a800671006cd20049840032b000a550000a800294800127000a4d0000980029280191f000e3d02807800285000508000a0c000c1400282000502000a00, 0x1d5a001aa400342800e81000cca01098401929000e510280a0003934007250006490000900038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0x258c010b140c0620006c1000d3a003a64027488016760024ea0001d000939000e6e000cd4000998009328000640024c40119380252681604c0024720048500090800060e00241800482000902001200, 0x3568016aa00ad520782a00034280168200a50207020002335004a6902c0d000599400b310016610000c000193400b250016490340900058f400b1d00023900007000585000b0800160c002c1000581000301001600, 0x359c003b3411066003ec9000d3c006a740004e001a9a002d2c003a4800747003e8a00050c006a1400042001a8200c4e401699802f3282006400347200685000309001a1000341800682000d02001a00, 0x3568006aa000d520a02a002d45005e89040110001a14003410006810001000019940033100666104c0c0001934003250006490480900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1b3800f668000cc003d94001b1801f610016be000d74001ad800f590002ae003d5a0002b000f55001e9a00ad24007a3803543006e8505410800b85800f0a001e10003c1800782000f02001e00, 0x1d9c010b180075d006ab200dd620a82c000756800eaa000d520002a000342800e81000cca01098400728800e4d000c920038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0xd6a001ac400346800689001cda0089a40032300064500008800190800320800040001c7c0028e80030a000610000c1800181800302000600, 0xc00480200802e00e00801800182c0000500400805800c01001006001004000, 0x6c5000d82001a740034c801676001ce40019b800335000266001cc40018500030800060e000c1800182000302000600, 0x458c001b141a0620022c1000d3a008a64011488016760044ea0001d00113900066e0044da0001b001135005266000cc401c95803b2a832054006c740088500110800060e00441800882001102002200, 0x356800eaa000d520e82a000342800e82001d020e0200039390076710640e0003994007310016610000c0003934007250006490000900018f40071d007a3906c07000385000708000e0c001c1000381000301000e00, 0xd9c001b341f0660006c9000d3c001a740004e00069a002d2c008a480034700068d000118001a2802943003e82010ce401f9b80413683c06c00747400185000309000610000c1800182000302000600, 0x35a8006b2000d621102c003f49008291078120001a34003450006890001100019b4003350042690840d0001954003290006510000a00018f80011d0006390800700018500030800060c000c1000181800302000600, 0x1b38003668000cc000d94001b18003610016be004574001ad80035a8000b4000d64003ab800f5500069a005524001a380034684608c001d0c0018580030a000610000c1800182000302000600, 0xd9c001b180035d0006b908c170001ad4003590006b1000160007aa800346800689000cda0059a40032a800652000ca200014001925000e3e0004740018500030800060c000c1000b81800302000600, 0xd7a00aae40034a802691002cbc0059740002e00165a002cb20001600072b002252002c9c00492800b0a001610000c1400582000b02001600, 0x1280480300804800e00c01800182c0000500600805800c01801007001006000, 0x6bd000d72001a5400348800675000ce20019580032900024e002c940018500030800060c002c1400182000302000600, 0x366802ac901158a001af40034f00269d000138009a6800b4b002695000128009a480074700228a00a50c003a080453b0006750980e80219a803131002252009c9400985000309002610004c1800982001302002600, 0xd7a001ae40454d000699098130001a54003490006910001200019d4003390016710000e00019580032900064e0004940018500030800060c000c1400182000302000600, 0x1b38015668000cc005594001b18015610016be00557a0002f00155d0006b6004564000ab800355002a9e00552c023a542704a002a8a00ad040018580150a002a1000541800a82001502002a00, 0xd9400ab080476084e0c0000d7a001ae80035c8000b8000d6c010ab80034c800695000d220019d4003390016710000e00019580032900064e0004940018500030800060c000c1400182000302000600, 0xd8a001b040033f00067d0000f80019e80033c800078000cec0099c80033700066a000ccc0069880030a00060e000c1800182000302000600, 0x1400480400804800e0100180b80280400401000601000800180c00001008000, 0x6ad000d52001a1400340801665000cc20019340032480023d000c720018500030800060c000c1000181000301000600, 0x1b38003668000cc000d94001b18003628000c4000d84001af80155d0006b6000d64000ab801f5500069e01253a1482700034b00068a003d0400b8580030a000610000c1800182000302000600, 0xd94024b24290640006c5000d84001b0400060002aba000d6c003ab80034e80069a000d3200026004549000676002ce40019b8003350006660004c40018500030800060e000c1800182000302000600, 0xd4c001a94000520006a2000d420002800034f00069a000d2c00aa480034700068a001d0c007a0801709000610000c1800182000302000600, 0x1400480500804a00e0140180c00280500401200601400800b80c0000100a000, 0x6ad000d52001a14017408016650134c200b9340032480963d00047200b85001708002e0c005c1000b81000301002e00],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT6 : List ℕ := [0x1c02038200681c, 0x1c00044200701a, 0x5c140001b06827, 0x1c0005c2706c1a, 0x2c00050270681b, 0x2400044200741b, 0x2c0005c2706c1a, 0x5000044200701a, 0x1c04044200701a, 0x440e01c1c06820, 0x3807044200701a, 0x1c000442c0801a, 0x1c0005c270741c, 0x2c02050270701d, 0x2c0205c270741c, 0x2c00044200701a, 0x2400050270681b, 0x101c0681a, 0x1c0702c1b0681a, 0x1c04038200681c, 0x1c0205c270741c, 0x500e044200701a, 0x101d0681a, 0x2c000001a0681a, 0x24040382006c1d, 0x2402050270701d, 0x500005c2706c1a, 0x50000001a0681a, 0x10000001a0681a, 0x1c0402c1d0681a, 0x24020382006c1d, 0x1c000081c06c1a, 0x1c000241c06c1a, 0x2404044200741b, 0x1c00044200741b, 0x38000001a0681a, 0x381b0681a, 0x1c02038290801c, 0x24000442d0801b, 0x10040101c0681a, 0x2c0b0101c0701a, 0x380e0101c0701a, 0x1c0402c1b0681a, 0x1c020382006c1d, 0x2400050270701d, 0x38070381b0681a]

def S6 (s i : ℕ) : List ℕ := unpackW wdT6 9 ((levT6.getD s []).getD i 0)

def N6 (s : ℕ) : ℕ := (levT6.getD s []).length

def A6 (s i tag : ℕ) : ℕ := findAct 4096 ((actT6.getD s []).getD i 0) tag

def W6 (w : ℕ) : ℕ := witT6.getD w 0

def Z6 (s : ℕ) := barrier 26 S6 N6 A6 W6 idRot s

theorem enc_inputs6 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT6) = xsT6 := by decide +kernel

theorem enc_goal6 : encL fT6 rowsT6 = goal 26 := by decide +kernel

theorem mask6 : mask 26 = 2 ^ rowsT6.length - 1 := by decide +kernel

theorem proper_fail6 : ∀ zs ∈ xsT6.sublists, zs ≠ xsT6 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked6 : ∀ s ≤ 7, ∀ i < N6 s, Z6 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun6 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 26) (goal 26) s xsT6) : False := by
  have hc : NatRun (mask 26) (goal 26) 7 xsT6 := extend_run h hs
  have p : xsT6.Perm (S6 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked6 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub6 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT6 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT6
  · subst e; exact noRun6 s hs h
  · exact proper_fail6 zs (List.mem_sublists.2 hz) e (required h)

theorem low6 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT6 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT6 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 26) (encL fT6 rowsT6) s' (ws.map fun a => encL a rowsT6) :=
    Run.map (fun a : BFn 5 => encL a rowsT6)
      (fun a => by rw [mask6]; exact encL_inv a rowsT6)
      (fun a b => encL_and a b rowsT6) (fun a b => encL_or a b rowsT6) hrun
  rw [enc_goal6] at hr
  refine no_sub6 s' (by omega) _ ?_ hr
  rw [← enc_inputs6]
  exact hsub.map _

def mono6 : List Gate := [⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.and, [5, 10]⟩, ⟨GateOp.or, [8, 11]⟩]

theorem mono_ok6 : ∀ g ∈ mono6, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono6, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval6 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono6, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve6 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfee8eee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono6, 12, mono_ok6, ?_, mono_eval6⟩
  by_contra hlt
  have hlen : mono6.length = 8 := rfl
  apply low6
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT7 : List ℕ := [1, 1, 1, 1, 2, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 5, 9, 17, 3, 5, 7, 14, 22, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT7 : List ℕ := [0x24c99fc00000f, 0x4b977440e1dd0, 0x9d3a78870e1e0, 0xf23fa1380fe00, 0xffe4423ff0000]

abbrev fT7 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT7 : List ℕ := [0x0, 0x100000000, 0x1cc0001ff, 0x1000000000, 0x1854001e1f, 0x8000000000, 0x889800e22f, 0x99dc00000f, 0x12200000000, 0x1220000fff0, 0x123cc00ffff, 0x13344001dd0, 0x13a5400ffff, 0x1a38800e1e0, 0x1aa9800ffff, 0x1ba1000fe00, 0x1bbdc00ffff, 0x80000000000, 0x81144000000, 0x9bbdc00ffff, 0xc00640f001f, 0x400000000000, 0x408188000000, 0x41bbdc00ffff, 0x4400a871002f, 0x4891cc000000, 0x4c01ec00000f, 0x900400000000, 0x9004007f01f0, 0x9005cc7f01ff, 0x9127000001c0, 0x9805440e01d0, 0x9937440001c0, 0x9c04647f01ff, 0xd005887001e0, 0xd1a7880001c0, 0xd404a87f01ff, 0xdc04207f0000, 0xdc05ec7f01ff, 0xdc15ec7f01ff, 0xdc85ec7f01ff, 0xddbe307ffe00, 0xddbffc7fffff, 0x2000000000000, 0x2009810000000, 0x201bbdc00ffff, 0x204083381020f, 0x2089954000000, 0x20c187400000f, 0x2409998000000, 0x24488b800000f, 0x24c0020000000, 0x24c1164000000, 0x24c81a8000000, 0x24c9830000000, 0x24c99fc00000f, 0x24d222000fff0, 0x24dbbfc00000f, 0x24dbbfc00ffff, 0x2909c107f01f0, 0x2952f338103cf, 0x2dc05ec7f01ff, 0x2dc9dfc00000f, 0x2dc9dfc7f01ff, 0x2ddbffc0001cf, 0x4204000000000, 0x42040038f1e10, 0x42058578f1e1f, 0x4217200001c00, 0x42850440e1c10, 0x4297344001c00, 0x42c40678f1e1f, 0x460c18b8f1e10, 0x46572a8711c2f, 0x4b166000e1dd0, 0x4b17700001dc0, 0x4b177440e1dd0, 0x4b844000e0000, 0x4b855440e0000, 0x4b8cc980ee22f, 0x4b967000e01c0, 0x4b967440e1dd0, 0x4b976000e1c00, 0x4b976440e1dd0, 0x4b97744001dc0, 0x4b977440e01c0, 0x4b977440e1c00, 0x4b977440e1dd0, 0x4b9f7440e1dd0, 0x4b9ffdc0effff, 0x4f977440e1dd0, 0x4f9f7cc0e1dd0, 0x4fd77ec7f1dff, 0x6205813801e00, 0x621fa10001c00, 0x62448338f1e1f, 0x62c40238f0000, 0x62c58778f1e1f, 0x62c59778f1e1f, 0x62cd8778f1e1f, 0x62de3ab8fe1e0, 0x62dfbff8fffff, 0x66c58778f1e1f, 0x66cd9fc00000f, 0x66cd9ff8f1e1f, 0x66dfbfc001c0f, 0x6b977440e1dd0, 0x6b9ff540e1dd0, 0x6bd7f778f1fdf, 0x6f05d9bf01fe0, 0x6f5eeb80e1ddf, 0x6f9ffdc0e1dd0, 0x6fc44200e0000, 0x6fc5dffff1fff, 0x6fcddfc0e000f, 0x6fd77640e1dd0, 0x6fdf7ec0e1dd0, 0x6fdff740e1dd0, 0x6fdfffc0e1ddf, 0x9020000000000, 0x9020003f1e220, 0x902889bf1e22f, 0x903a20000e000, 0x90a1147f1e220, 0x90fa2640fe01f, 0x942808870e020, 0x943a38800e000, 0x94600abf1e22f, 0x993260070e1e0, 0x993a70000e1c0, 0x993a78870e1e0, 0x9d20400700000, 0x9d21c54701e1f, 0x9d28588700000, 0x9d327007001c0, 0x9d3278870e1e0, 0x9d3a60070e000, 0x9d3a68870e1e0, 0x9d3a78800e1c0, 0x9d3a7887001c0, 0x9d3a78870e000, 0x9d3a78870e1e0, 0x9d3b78870e1e0, 0x9d3bfdc70ffff, 0x9dba78870e1e0, 0x9dbb7cc70e1e0, 0x9dfa7ec7fe1ff, 0xb02881380e200, 0xb03ba1000e000, 0xb060833f1e22f, 0xb460023f10000, 0xb4688bbf1e22f, 0xb4689bbf1e22f, 0xb4698bbf1e22f, 0xb473367f11dd0, 0xb47bbfff1ffff, 0xb4e88bbf1e22f, 0xb4e99fc00000f, 0xb4e99fff1e22f, 0xb4fbbfc00e00f, 0xb9a8d578ee3d0, 0xb9f3e7470e1ef, 0xbd3a78870e1e0, 0xbd3bf9870e1e0, 0xbd7afbbf1e3ef, 0xbdbbfdc70e1e0, 0xbde0420700000, 0xbde8dffffe3ff, 0xbde9dfc70000f, 0xbdfa7a870e1e0, 0xbdfb7ec70e1e0, 0xbdfbfb870e1e0, 0xbdfbffc70e1ef, 0xd23620380fe00, 0xd23f20000fc00, 0xd23fa1380fe00, 0xd6ad0cc7efc30, 0xd6f63ef80fe0f, 0xdb24403ff0000, 0xdb2dddfff000f, 0xdb36603fffff0, 0xdb3ffdfffffff, 0xdbb77440e1dd0, 0xdbb7747fffff0, 0xdbbf7440efdd0, 0xdf3e78870e1e0, 0xdf3e78bfffff0, 0xdf3f78870fde0, 0xdfa44007e0000, 0xdfb77447e1dd0, 0xdfbe7887ee1e0, 0xdfbf7cc7efdf0, 0xdfe4423ff0000, 0xdff67efffffff, 0xf224003800000, 0xf2241cf8001ff, 0xf22d813800000, 0xf237203801c00, 0xf237a1380fe00, 0xf23e20380e000, 0xf23ea1380fe00, 0xf23fa1000fc00, 0xf23fa13801c00, 0xf23fa1380e000, 0xf23fa1380fe00, 0xf23fb1380fe00, 0xf23fbdf80ffff, 0xf2bfa1380fe00, 0xf2bfb5780fe00, 0xf2ffa778ffe1f, 0xf63fa1380fe00, 0xf63fb9b80fe00, 0xf67fabbf1fe2f, 0xf6bfbdf80fe00, 0xf6e4023800000, 0xf6ed8fffffe3f, 0xf6ed9ff80000f, 0xf6ffa3380fe00, 0xf6ffb7780fe00, 0xf6ffbbb80fe00, 0xf6ffbff80fe0f, 0xfb3fe1380fe00, 0xfb3fe13fffff0, 0xfb3ff1380ffc0, 0xfba44038e0000, 0xfbb77478e1dd0, 0xfbbfe138efe00, 0xfbbff578effd0, 0xfbe4423ff0000, 0xfbf7e77ffffff, 0xff24403f00000, 0xff3e78bf0e1e0, 0xff3fe13f0fe00, 0xff3ff9bf0ffe0, 0xff64423ff0000, 0xff7eebbffffff, 0xffbffdffefff0, 0xffe44207e0000, 0xffe44238e0000, 0xffe4423f00000, 0xffe4423ff0000, 0xffe4523ff0000, 0xffe45efff01ff, 0xffe5423ff0000, 0xffe5567ff0000, 0xffe5c77ff1e1f, 0xffec423ff0000, 0xffec5abff0000, 0xffeccbbffe22f, 0xffed5efff0000, 0xffedc33ff0000, 0xffedd77ff0000, 0xffeddbbff0000, 0xffeddffff000f, 0xfff6623ff0000, 0xfff6623fffff0, 0xfff6723ff01c0, 0xfff7623ff1c00, 0xfff7767ff1dd0, 0xfffe623ffe000, 0xfffe7abffe1e0, 0xffff7effffdf0, 0xffffe33fffe00, 0xfffff77ffffd0, 0xfffffbbffffe0, 0xffffffc7efdff, 0xfffffff8effdf, 0xffffffff0ffef, 0xfffffffff1ddf, 0xfffffffffe1ef, 0xffffffffffe0f, 0xfffffffffffff]

def levT7 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x3c4cd2386f, 0x3c4d124877, 0x3d4cd24877, 0x3d4d123877, 0x3c4cd2387c, 0x3c4cd28858, 0x3c4d42b45c, 0x3e0cd2b45c, 0x3e0d42b458, 0x3c4cd16049, 0x3c4b223858, 0x3c4dd2906c, 0x3ecdd2386c, 0x3ecdd29058, 0x3c48e1603c, 0x334b423858, 0x3f8cd2a874, 0x3f8da23874, 0x3f8da2a858, 0x3348e16039, 0x3c4cd2c438, 0x3c4cd0f438, 0x3c4a123838, 0x3c48e12838, 0x3349b23838, 0x3348e14038, 0x3c46e16038, 0x3c47d16038, 0x3346516038, 0x3348516038, 0x238580e02a, 0x3108e16038],
  [0xf13348e16038, 0xf1334b523858, 0xf13349823838, 0xf13346216038, 0xf1238580e027, 0xcd238580e011, 0xf1334b52608e, 0xf1334b518858, 0xf12d48e16027, 0xcd2d48e16011, 0xf13348e1dc13, 0xf13349216038, 0xf13448e16038, 0xf53348e16038, 0xf1334ad16017, 0xf13348e17038, 0xf13508e16038, 0xf83348e16038, 0xf13748e1602d, 0xf13348e1b038, 0xf1334a416038, 0xfb3348e16038, 0xfe3348e16034, 0xf13348e1d038, 0xf1334aa16038, 0xf13688e16038, 0xf13349818838, 0xf12608e0e027, 0xcd2608e0e011, 0xf1334c00e01f, 0xf13908e11438, 0x1033348e13838, 0xf1188580e027, 0xcd188580e011, 0xf13a87b16038, 0x1053348416038, 0x8e1603809c11, 0x10730c8e16038, 0xf1334b526062, 0xf12d49823827, 0xcd2d49823811, 0xf1334c02d41f, 0xf1334b82384b, 0xf1390b523845, 0x103334b52384e, 0xf12d46216027, 0xcd2d46216011, 0xf1334bb20458, 0xf13a8b51ec58, 0x105334b521058, 0xf137cae23858, 0x100334b323858, 0xb52385809c11, 0x10730cb523858, 0xf1334b524858, 0xf1344b523858, 0xf5334b523858, 0xf1334b52385c, 0xf1350b523858, 0xf8334b523858, 0xf1334b52386c, 0xf1334b529058, 0xfb334b523858, 0xf1334b523874, 0xf1334b52a858, 0xf1368b523858, 0xf13b0cd23877, 0xf1334921dc13, 0xf13448e1dc13, 0xf53348e1dc13, 0xf13348e1e413, 0xf13347718813, 0xf12387709c13, 0xcd2387704c11, 0xf1334921dc38, 0xf13448e1dc38, 0xf53348e1dc38, 0xf13348e1dc1a, 0xf1334c00e024, 0xf13348e1dc30, 0xf13908e17c38, 0xf13348e1dc35, 0x1033348e1c438, 0xf13288e16038, 0xee3348e16038, 0xf13348b16038, 0xef3348e16038, 0xf13348c16038, 0xf132c8e16038, 0xf13348a16038, 0xf13248e16038, 0xeb3348e16038, 0xf13349824838, 0xf13346016038, 0xf1248580e027, 0xcd248580e011, 0xf13449216038, 0xf53349216038, 0xf13388e16038, 0xf23348e16038, 0xf13449823838, 0xf13446216038, 0xf1238580e025, 0xd1238580e011, 0xf53448e16038, 0xf13348f16038, 0xf43348e16038, 0xf53349823838, 0xf53346216038, 0xf5238580e027, 0xcd238580e00f, 0xf13349116038, 0xf13408e16038, 0xf13346316038, 0xf1238580e028, 0xcd238580e014, 0xf1398cd2b458, 0xf1334ad17017, 0xf1350ad16017, 0xf8334ad16017, 0xf1334ad26017, 0xf13345810c17, 0xf12b45809c17, 0xcd2b45805c11, 0xf1334ad17038, 0xf1350ad16038, 0xf8334ad16038, 0xf1334ad1601a, 0xf1334c00e021, 0xf1334ad16032, 0xf13a89516038, 0xf1334ad16036, 0x105334a716038, 0xf13348e15438, 0xf03348e16038, 0xf13348e15838, 0xf13308e16038, 0xf13348e15038, 0xf131c8e16038, 0xe53348e16038, 0xf13349623838, 0xf13346217038, 0xf12385c0e027, 0xcd2385c0e011, 0xf13508e17038, 0xf83348e17038, 0xf13509823838, 0xf13506216038, 0xf1238580e022, 0xd4238580e011, 0xf83508e16038, 0xf13348e16438, 0xf73348e16038, 0xf83349823838, 0xf83346216038, 0xf8238580e027, 0xcd238580e00d, 0xf13348e16c38, 0xf134c8e16038, 0xf13349923838, 0xf1238580e029, 0xcd238580e018, 0xf1374c223858, 0xf13748e1b02d, 0xf1374a41602d, 0xfb3748e1602d, 0xf1374982382d, 0xf1374621602d, 0xf1238580b41d, 0xdd238580b411, 0xf13748e1b038, 0xf1374a416038, 0xfb3748e16038, 0xf13748e16030, 0xf13908e11c38, 0xf13748e16032, 0xf13a87f16038, 0xf13748e16037, 0x10735c8e16038, 0xf13348e15c38, 0xf13348d16038, 0xf13348e14838, 0xf13348816038, 0xcd3048e16038, 0xf13348e20038, 0xf13346c18838, 0xf12386c0e027, 0xcd2386c0e011, 0xf1334a41b038, 0xfb3348e1b038, 0xf1334a426038, 0xf13345812038, 0xf1290580e027, 0xcd290580e011, 0xfb334a416038, 0xfb3349823838, 0xfb3346216038, 0xfb238580e027, 0xcd238580e00b, 0xf13348e1ac38, 0xf1334a316038, 0xf13349a23838, 0xf13346416038, 0xcd238580e02e, 0xfe334b623858, 0xfe3348e1d034, 0xfe334aa16034, 0xfe3688e16034, 0xfe3349823834, 0xfe3346216034, 0xfe238580d027, 0xcd238580d00a, 0xfe3348e1d038, 0xfe334aa16038, 0xfe3688e16038, 0xfe3348e16035, 0x1033348e13c38, 0xfe3348e16036, 0x1053348616038, 0xfe3348e16037, 0x1073148e16038, 0xf13348e13438, 0xf13348316038, 0xf12c08e16038, 0xf13348e1e838, 0xf13347418838, 0xf1238740e027, 0xcd238740e011, 0xf1334aa1d038, 0xf13688e1d038, 0xf1334aa26038, 0xf13345811038, 0xf12a8580e027, 0xcd2a8580e011, 0xf1368aa16038, 0xf13689823838, 0xf13686216038, 0xf1238580e01e, 0xda238580e011, 0xf13349d23838, 0xf13346716038, 0xf1238580f838, 0xf13349f23833, 0xf1260620e027, 0xcd260620e011, 0xf1334a51f838, 0xf13a8981ec38, 0x1053349821038, 0xf13549423838, 0xf93349723838, 0x982383809c11, 0x10730c9823838, 0xf13588e16038, 0xfa3348e16038, 0xf1360cd30038, 0xf1334c010438, 0xf1334380bc1f, 0xf13003809c1f, 0xcd3003807c11, 0xf13348e1603a, 0xff3348e16038, 0xf13348e1603f, 0xf13788e16038, 0xf1334a616038, 0xfc3348e16038, 0xf13908e1a838, 0xf1390a823838, 0xf13906211438, 0xf1238450e019, 0xe4238450e011, 0xf13348e1a058, 0xf1334ba16038, 0xf1334ab16038, 0xf136c8e16038, 0x1033348e1cc38, 0x1033349c23838, 0x1033346213838, 0x1032384e0e027, 0xcd2384e0e007, 0xf13346916031, 0xf13346d11838, 0xf13485e16038, 0xf63346116038, 0x621603809c11, 0x10730c6216038, 0xf13348e1c038, 0xfd3348e16038, 0xf13a8a016038, 0xf13a87216038, 0xf11ec580e015, 0xea1ec580e011, 0xf13349e23858, 0xf1334b723838, 0xf13348e1d438, 0xf13708e16038, 0x105334a916038, 0x1053346616038, 0x105210580e027, 0xcd210580e005, 0xf1238581001b, 0xf12385d0e020, 0xf124c580e023, 0xf3238580e026, 0xf13348e1d838, 0xf1334ac16038, 0x1073648e16038, 0x107238580e02b, 0xc3238580e003, 0xcd238580ec08, 0xcd2385a0e00c, 0xcd240580e00e, 0xcf238580e010],
  [0xf13348e16038, 0x3c4cd238580e038, 0xf1334b523858, 0x3c4cd2d48e16038, 0x3c4cd2387716038, 0x3c4cd238580e013, 0x3c4cd2b48e16038, 0x3c4cd238580e017, 0x3c4dd3348e16038, 0x3c4cd238580e02d, 0x3f8f13348e16038, 0x3c4cd238580e034, 0x3c4cd2385816038, 0xf13349823838, 0x3c4cd2608e16038, 0x3c4cd3008e16038, 0x3c4cd238580e01f, 0x3c4e43348e16038, 0x3c4cd2385811438, 0x40cf13348e16038, 0x3c4cd2385813838, 0x3c4cd2388e16038, 0xf13346216038, 0x3c4cd2386216038, 0x3c4ea3348e16038, 0x3c4cd2387b16038, 0x414f13348e16038, 0x3c4cd2388416038, 0x3c4cd3348e16038, 0xf1238580e027, 0x3c4cd238580e027, 0x41cf13348e16038, 0x3c4cd30c8e16038, 0x3c4f13348e16038, 0xcd238580e011, 0x3c4cd238580e011, 0x3c4cd2608e0e038, 0x3c4cd188580e038, 0x3c48e160380e027, 0x3348e160380e011, 0x3c4cd2d48e16058, 0xf1334b52608e, 0x3c4cd2d49823858, 0x3c4cd300b523858, 0x3c4cd2d48e1601f, 0x3c4cd2e0b523858, 0x3c4cd2d48e1604b, 0x3c4e4334b523858, 0x3c4cd2d48e16045, 0x40cf1334b523858, 0x3c4cd2d48e1604e, 0x3c4cd2d48e23858, 0xf1334b518858, 0x3c4cd2d48e18858, 0x3c4cd2ecb523858, 0x3c4cd2d48e20458, 0x3c4ea334b523858, 0x3c4cd2d48e1ec58, 0x414f1334b523858, 0x3c4cd2d48e21058, 0x3c4cd2d4b523858, 0x3c4df334b523858, 0x3c4cd2d4ae23858, 0x400f1334b523858, 0x3c4cd2d4b323858, 0x3c4cd334b523858, 0xf12d48e16027, 0x3c4cd2d48e16027, 0x41cf1334b523858, 0x3c4cd30cb523858, 0x3c4f1334b523858, 0xcd2d48e16011, 0x3c4cd2d48e16011, 0x3c4cd2d48e1dc58, 0x3c4cd2d48e16013, 0x3c4cd2d4ad23858, 0x3c4cd2d48e16017, 0x440f13348e16038, 0x440f1334b523858, 0x3c4cd238580e001, 0x3c4cd2d48e16001, 0x3c4dd334b523858, 0x3c4cd2d48e1602d, 0x3f8f1334b523858, 0x3c4cd2d48e16034, 0x3c4cd2d49823838, 0x3c4cd2e08e16038, 0x3c4cd2385812c38, 0x3c4cd2d46216038, 0x3c4cd2ec8e16038, 0x3c4cd2388116038, 0x3c4df3348e16038, 0x3c4cd2b88e16038, 0x400f13348e16038, 0x3c4cd2cc8e16038, 0x3c4b5238580e027, 0x334b5238580e011, 0xf13348e1dc13, 0x3c4cd238770e013, 0x3c4cd2387716013, 0x3c4cd2608e1dc38, 0x3c4cd3008e1dc38, 0x3c4e43348e1dc38, 0x40cf13348e1dc38, 0x3c4cd2387916038, 0x428f13348e16038, 0x3c4cd238580e024, 0x42cf13348e16038, 0x3c4cd2385f16038, 0x434f13348e16038, 0x3c4cd2387116038, 0x3c4cd1dc6216038, 0x3c48e1dc580e027, 0x3348e1dc580e011, 0x3c4ec3348e16038, 0xf13349216038, 0x3c4cd248580e013, 0x3c4cd2488e16038, 0x3c4cd238580e002, 0xf13448e16038, 0x3c4d1238580e013, 0x3c4d13348e16038, 0x3c4cd238580e004, 0xf53348e16038, 0x3d4cd238580e013, 0x3d4f13348e16038, 0x3c4cd238580e012, 0x3c4cd2608e0e013, 0x3c4cd188580e013, 0x3c48e1603809c13, 0x3348e1603804c11, 0xf1334ad16017, 0x3c4cd2b4580e017, 0x3c4cd2b48e16017, 0x3c4cd2b49823838, 0x3c4cd300ad16038, 0x3c4cd238580e021, 0x3c4cd2b46216038, 0x3c4ea334ad16038, 0x414f1334ad16038, 0x3c4cd2385810c38, 0x430f13348e16038, 0x3c4cd2548e16038, 0x438f13348e16038, 0x3c4cd29c8e16038, 0x3c4ad238580e027, 0x334ad238580e011, 0x3c4e63348e16038, 0xf13348e17038, 0x3c4cd2385c0e017, 0x3c4cd2385c16038, 0xf13508e16038, 0x3c4d4238580e017, 0x3c4d43348e16038, 0x3c4cd238580e006, 0xf83348e16038, 0x3e0cd238580e017, 0x3e0f13348e16038, 0x3c4cd238580e016, 0x3c4cd2608e0e017, 0x3c4cd188580e017, 0x3c48e1603809c17, 0x3348e1603805c11, 0xf13748e1602d, 0x3c4dd238580e02d, 0x3c4dd3348e1602d, 0x3c4dd3349823838, 0x3c4e43748e16038, 0x3c4cd2385811c38, 0x3c4dd3346216038, 0x3c4ea3748e16038, 0x3c4cd2387f16038, 0x3c4dd238580e027, 0x41cf13748e16038, 0x3c4cd238580e01d, 0x43cf13348e16038, 0x3c4d73348e16038, 0x374cd238580e011, 0x3c4cd3088e16038, 0xf13348e1b038, 0x3c4cd2386c0e02d, 0x3c4cd2386c16038, 0xf1334a416038, 0x3c4cd290580e02d, 0x3c4cd2908e16038, 0xfb3348e16038, 0x3eccd238580e02d, 0x3ecf13348e16038, 0x3c4cd238580e02c, 0x3c4cd2608e0e02d, 0x3c4cd188580e02d, 0x3c48e160380b427, 0x3348e160380b411, 0xfe3348e16034, 0x3f8cd238580e034, 0x3f8f13348e16034, 0x3f8f13349823838, 0x40cfe3348e16038, 0x3c4cd2385813c38, 0x3f8f13346216038, 0x414fe3348e16038, 0x3c4cd2388616038, 0x3f8f1238580e027, 0x41cfe3348e16038, 0x3c4cd3148e16038, 0x3f8cd238580e011, 0x3c4cd238580e00a, 0x3c4cd2d88e16038, 0xf13348e1d038, 0x3c4cd238740e034, 0x3c4cd2387416038, 0xf1334aa16038, 0x3c4cd2a8580e034, 0x3c4cd2a88e16038, 0xf13688e16038, 0x3c4da238580e034, 0x3c4da3348e16038, 0x3c4cd2608e0e034, 0x3c4cd188580e034, 0x3c48e160380d027, 0x3348e160380d011, 0x3c4cd1885816038, 0x3c48e160580e027, 0x3348e160580e011, 0x3c4cd27c9823838, 0x3c4cd2608e0e033, 0x3c4cd2608e23838, 0xf13349818838, 0x3c4cd2608e18838, 0x3c4cd2949823838, 0x3c4cd2608e1f838, 0x3c4ea3349823838, 0x3c4cd2608e1ec38, 0x414f13349823838, 0x3c4cd2608e21038, 0x3c4cd2609823838, 0x3c4d53349823838, 0x3c4cd2609423838, 0x3e4f13349823838, 0x3c4cd2609723838, 0x3c4cd3349823838, 0xf12608e0e027, 0x3c4cd2608e0e027, 0x41cf13349823838, 0x3c4cd30c9823838, 0x3c4f13349823838, 0xcd2608e0e011, 0x3c4cd2608e0e011, 0x3c4cd27c8e16038, 0x3c4cd238580e033, 0x3c4cd3009823838, 0x3c4cd2608e0e01f, 0x440f13349823838, 0x3c4cd2608e0e001, 0x3c4e43349823838, 0x3c4cd2608e11438, 0x40cf13349823838, 0x3c4cd2608e13838, 0x3c4cd2606216038, 0x3c4cd2948e16038, 0x3c4cd2387e16038, 0x3c4d53348e16038, 0x3c4cd2508e16038, 0x3e4f13348e16038, 0x3c4cd25c8e16038, 0x3c498238580e027, 0x33498238580e011, 0x3c4cd238580e01a, 0xf1334c00e01f, 0x3c4cd300580e01f, 0x3c4cd3008e0e01f, 0x3c4cd3006216038, 0x3c4cd238580e02f, 0x3c4ed3348e16038, 0x3c4cd2bc8e16038, 0x418f13348e16038, 0x3c4cd2f48e16038, 0x3c4c0238580e027, 0x1073c4cd3008e16038, 0x334c0238580e011, 0x3c4d83348e16038, 0x3c4cd2385810438, 0x3c4e03348e16038, 0x3c4cd238580e009, 0x404f13348e16038, 0x3c4cd238580e01c, 0x3c4cd188580e01f, 0x3c48e1603809c1f, 0x3348e1603807c11, 0x3c4cd238580e030, 0xf13908e11438, 0x3c4e42385811438, 0x3c4e43348e11438, 0x3c4e43346216038, 0x3c4cd2388216038, 0x1053c4e43348e16038, 0x3c4e4238580e027, 0x3c4cd238580e019, 0x420f13348e16038, 0x3c4e13348e16038, 0x390cd238580e011, 0x3c4cd2386a16038, 0x3c4cd2a08e16038, 0x3c4cd2f08e16038, 0x408f13348e16038, 0x3c4cd2385810838, 0x3c4cd1885811438, 0x3c48e160450e027, 0x3348e160450e011, 0x3c4cd238580e035, 0x1033348e13838, 0x40ccd2385813838, 0x40cf13348e13838, 0x40cf13346216038, 0x1033c4ea3348e16038, 0x3c4cd2388716038, 0x40cf1238580e027, 0x3c4cd3188e16038, 0x40ccd238580e011, 0x3c4cd238580e007, 0x3c4cd2387316038, 0x3c4cd2708e16038, 0x3c4cd2fc8e16038, 0x3c4e33348e16038, 0x3c4cd1885813838, 0x3c48e1604e0e027, 0x3348e1604e0e011, 0x3c48e238580e027, 0x3348e238580e011, 0x3c4cd1a46216038, 0x3c4cd188580e031, 0x3c4cd1b46216038, 0x3c4cd1885811838, 0x3c4cd1886216038, 0x3c4d23346216038, 0x3c4cd1885e16038, 0x3d8f13346216038, 0x3c4cd1886116038, 0x3c4cd3346216038, 0xf1188580e027, 0x3c4cd188580e027, 0x41cf13346216038, 0x3c4cd30c6216038, 0x3c4f13346216038, 0xcd188580e011, 0x3c4cd188580e011, 0x3c4cd2386916038, 0x3c4cd238580e031, 0x3c4cd2386d16038, 0x3c4cd2385811838, 0x440f13346216038, 0x3c4cd188580e001, 0x3c4d23348e16038, 0x3c4cd2385e16038, 0x3d8f13348e16038, 0x3c4cd2386116038, 0x3c4ea3346216038, 0x3c4cd1ec6216038, 0x414f13346216038, 0x3c4cd2106216038, 0x3c48e188580e027, 0x3348e188580e011, 0x3c4cd238580e032, 0x3c4cd2385813038, 0xf13a87b16038, 0x3c4ea2387b16038, 0x3c4ea3347b16038, 0x3c4ea238580e027, 0x3c4cd238580e015, 0x424f13348e16038, 0x3c4e73348e16038, 0x3a8cd238580e011, 0x3c4cd2808e16038, 0x3c4cd2e48e16038, 0x3c4cd2387216038, 0x410f13348e16038, 0x3c4cd2387816038, 0x3c48e1ec580e027, 0x3348e1ec580e011, 0x3c4cd238580e036, 0x3c4cd2385814438, 0x1053348416038, 0x414cd2388416038, 0x414f13348416038, 0x414f1238580e027, 0x3c4cd3208e16038, 0x414cd238580e011, 0x3c4cd238580e005, 0x3c4cd2a48e16038, 0x3c4cd2f88e16038, 0x3c4cd2386616038, 0x3c4e93348e16038, 0x3c48e210580e027, 0x3348e210580e011, 0x334cd238580e011, 0x3c48e1603809c27, 0x3c48e160400e027, 0x3c48e1603809c1b, 0x3c48e174580e027, 0x3c48e1603809c20, 0x3c493238580e027, 0x3c48e1603809c23, 0x3ccf1238580e027, 0x3c48e1603809c26, 0x3c4f1238580e027, 0x8e1603809c11, 0x3c48e1603809c11, 0x3c4cd2385810038, 0x3c4cd238580e01b, 0x3c4cd2385d16038, 0x3c4cd238580e020, 0x3c4cd24c8e16038, 0x3c4cd238580e023, 0x440f1238580e027, 0x3c48e1603809c01, 0x3ccf13348e16038, 0x3c4cd238580e026, 0x41cf1238580e027, 0x3c4c3238580e027, 0x3348e1603809c11, 0x3c4cd238580e037, 0x3c4cd2385814c38, 0x3c4cd2388916038, 0x10730c8e16038, 0x41ccd30c8e16038, 0x41cf130c8e16038, 0x41ccd238580e011, 0x3c4cd238580e003, 0x3c4d93348e16038, 0x3c4e23348e16038, 0x3c4e83348e16038, 0x3c4cd238580e02b, 0x334c3238580e011, 0x3348e1603804411, 0x3348e1603b0e011, 0x3348e1603804408, 0x3348e168580e011, 0x3348e160380440c, 0x33490238580e011, 0x3348e160380440e, 0x33ccd238580e011, 0x3348e1603804410, 0x3c4cd238580ec38, 0x3c4cd238580e008, 0x3c4cd2385a16038, 0x3c4cd238580e00c, 0x3c4cd2408e16038, 0x3c4cd238580e00e, 0x3c4cf3348e16038, 0x3c4cd238580e010, 0x440cd238580e011, 0x3348e1603804401],
  [0xf13348e16038, 0x3c4cd238580e038, 0xf1334b523858, 0x3c4cd2d48e16038, 0x3c4cd2387716038, 0x3c4cd238580e013, 0x3c4cd2b48e16038, 0x3c4cd238580e017, 0x3c4dd3348e16038, 0x3c4cd238580e02d, 0x3f8f13348e16038, 0x3c4cd238580e034, 0x3c4cd2385816038, 0xf13349823838, 0x3c4cd2608e16038, 0x3c4cd3008e16038, 0x3c4cd238580e01f, 0x3c4e43348e16038, 0x3c4cd2385811438, 0x40cf13348e16038, 0x3c4cd2385813838, 0x3c4cd2388e16038, 0xf13346216038, 0x3c4cd2386216038, 0x3c4ea3348e16038, 0x3c4cd2387b16038, 0x414f13348e16038, 0x3c4cd2388416038, 0x3c4cd3348e16038, 0xf1238580e027, 0x3c4cd238580e027, 0x41cf13348e16038, 0x3c4cd30c8e16038, 0x3c4f13348e16038, 0xcd238580e011, 0x3c4cd238580e011],
  [0xf13348e16038]]

def actT7 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x0, 0x38c180718200e30201c600, 0x394180728200e50201ca00, 0x39c180738200e70201ce00, 0x0, 0x0, 0x1ac1803582006b0200d600, 0x1ac1803582006b0200d600, 0x1ac1803582006b0200d600, 0x0, 0x0, 0x1b41803682006d0200da00, 0x1b41803682006d0200da00, 0x1b41803682006d0200da00, 0x0, 0x0, 0x1bc1803782006f0200de00, 0x1bc1803782006f0200de00, 0x1bc1803782006f0200de00, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0],
  [0x1e10003c1800782000f02001e00, 0x1e0a, 0x1e0a, 0x1e0a, 0x1e02, 0x1e02, 0x0, 0x0, 0x0, 0x0, 0x7b4100f26201dc9403a8f40751d00ea1001d41803a8200750200ea00, 0xd71d002610004c1800982001302002600, 0xd91d003a1000741800e82001d02003a00, 0xdb1d002610004c1800982001302002600, 0x6b4100d66201ac9a03592806b1d00d61001ac1803582006b0200d600, 0x4125002e10005c1800b82001702002e00, 0x1525001e10003c1800782000f02001e00, 0x4125002e10005c1800b82001702002e00, 0x6d4100da6501b4c403692806d1d00da1001b41803682006d0200da00, 0x1931001e10003c1800782000f02001e00, 0x1931001e10003c1800782000f02001e00, 0x1931001e10003c1800782000f02001e00, 0x6f4280de8201bcc403792806f1d00de1001bc1803782006f0200de00, 0x1b41001e10003c1800782000f02001e00, 0x1b41001e10003c1800782000f02001e00, 0x1b41001e10003c1800782000f02001e00, 0x0, 0x0, 0x0, 0x849a0109280071c80421000841801082002102004200, 0x8cda0119a80071d004610008c1801182002302004600, 0x3d1a007a280011d001e10003c1800782000f02001e00, 0x0, 0x0, 0x3cea0079c800d25001e10003c1800782000f02001e00, 0x3d2a007a4800125001e10003c1800782000f02001e00, 0x0, 0x3d3a007a6800131001e10003c1800782000f02001e00, 0x0, 0x0, 0x0, 0x4206, 0x0, 0x460a, 0x1e0a, 0x0, 0x0, 0x0, 0x1e0a, 0x1e0a, 0x0, 0x0, 0x0, 0x1e0a, 0x260a, 0x3a0a, 0x260a, 0x2e0a, 0x1e0a, 0x2e0a, 0x1e0a, 0x1e0a, 0x1e0a, 0x1e0a, 0x1e0a, 0x1e0a, 0x3200ea0e, 0x39a080774080408001ccc403b9840103000ee4d01dc9403b8f40771d00ee1001dc1803b8200770200ee00, 0x39a080dd4080608001e4ca03c9880732500ee4900409003c8f40791d00f21001e41803c8200790200f200, 0x3da1407b4100e6620374c20181800732500ee4900809003d8f407b1d00f61001ec1803d82007b0200f600, 0x401c00ea06, 0xea06, 0xea06, 0xea02, 0xd74080fe61037c9a06b8f40d71d01ae10035c1806b8200d70201ae00, 0xd94080f26501d49206c8f40d91d01b21003641806c8200d90201b200, 0x7b4281b66101d49206d8f40db1d01b610036c1806d8200db0201b600, 0xe141018262037c9403f8f407f1d00fe1001fc1803f82007f0200fe00, 0x849a0109280071c80421000841801082002102004200, 0x7b4100f26201dc9403a8f40751d00ea1001d41803a8200750200ea00, 0x8cda0119a80071d004610008c1801182002302004600, 0x7b4100f26201dc9403a8f40751d00ea1001d41803a8200750200ea00, 0x3d1a007a280011d001e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x4610008c1801182002302004600, 0x4610008c1801182002302004600, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x260a, 0x260a, 0x2602, 0x2602, 0x94740718e40101c002610004c1800982001302002600, 0x94740728e40201c002610004c1800982001302002600, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x3a0a, 0x3a0a, 0x3a02, 0x3a02, 0x94740738e40301c002610004c1800982001302002600, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x260a, 0x260a, 0x2602, 0x2602, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e0a, 0x1e02, 0x1e02, 0x503600d60e, 0x35a0806b4080e08001acc40359840603000d64d01ac940358f406b1d00d61001ac1803582006b0200d600, 0x35a0806b4081008001acca03598806b2680d64a01ac740448e40601c00d61001ac1803582006b0200d600, 0x35a1406b4100d66201acc204018006b2680d64a01ac740448e40701c00d61001ac1803582006b0200d600, 0xd606, 0x901c00d606, 0xd606, 0xd602, 0x4140811e6101049a02092808d1e80821001041802082004102008200, 0x154080d66500549a00a92806b1c802a1000541800a82001502002a00, 0x6b42811e6101049a02092806b1c80821001041802082004102008200, 0xeb4101d262024c9a04992808d1d012610024c1804982009302012600, 0x2d49a05a9280071c816a1002d41805a8200b502016a00, 0x6b4100d66201ac9a03592806b1d00d61001ac1803582006b0200d600, 0x3cea0079c800d25001e10003c1800782000f02001e00, 0x6b4100d66201ac9a03592806b1d00d61001ac1803582006b0200d600, 0x3d2a007a4800125001e10003c1800782000f02001e00, 0x2a1000541800a82001502002a00, 0x1e10003c1800782000f02001e00, 0x2a1000541800a82001502002a00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x2e0a, 0x2e0a, 0x2e02, 0x2e02, 0x1049403592406024002e10005c1800b82001702002e00, 0x1049403592407024002e10005c1800b82001702002e00, 0x1e0a, 0x1e0a, 0x1e02, 0x1e02, 0x1049403592408024002e10005c1800b82001702002e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x2e0a, 0x2e0a, 0x2e02, 0x2e02, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e0a, 0x1e02, 0x1e02, 0xa03a00da0a, 0x36a0806d4081808001b4ca03698806d2500da4902c0900368f406d1d00da1001b41803682006d0200da00, 0x36a0806d4081a08001b4ca03698806d2680da4a01b47404b8e40b01c00da1001b41803682006d0200da00, 0x36a1406d4100da6501b4c403692806d2481a04801b47404b8e40c01c00da1001b41803682006d0200da00, 0xda0a, 0xda0a, 0xe01c00da02, 0xda02, 0x19408032650064c404e92409b1e80321000641800c82001902003200, 0x19408032650064c403693406d1c80321000641800c82001902003200, 0x6d428032650064c404e92406d1c80321000641800c82001902003200, 0xed41013665026cc407692809b1d013610026c1804d82009b02013600, 0x74da00e9a80071d003a1000741800e82001d02003a00, 0x6d4100da6501b4c403692806d1d00da1001b41803682006d0200da00, 0x3cea0079c800d25001e10003c1800782000f02001e00, 0x6d4100da6501b4c403692806d1d00da1001b41803682006d0200da00, 0x3d3a007a6800131001e10003c1800782000f02001e00, 0x321000641800c82001902003200, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e06, 0x1e06, 0x1e02, 0x1e02, 0x64c40369840b030001e10003c1800782000f02001e00, 0x64c40369840c030001e10003c1800782000f02001e00, 0x1e06, 0x1e06, 0x1e02, 0x1e02, 0x64c40369840d030001e10003c1800782000f02001e00, 0x1e0a, 0x1e0a, 0x1e02, 0x1e02, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e0a, 0x1e0a, 0x1e02, 0xf04a00de0a, 0x37a1406f4100de6201bcc208818006f2500de490400900378f406f1d00de1001bc1803782006f0200de00, 0x37a1406f4100de6201bcc209018006f2680de4a01bc740518e41001c00de1001bc1803782006f0200de00, 0x37a1406f4100de6501bcc403792806f2482404801bc740518e41101c00de1001bc1803782006f0200de00, 0xde0a, 0xde0a, 0xde02, 0x1301c00de02, 0x1b428036820064c200a9240a71e803610006c1800d82001b02003600, 0x1b428036820064c203793406f1c803610006c1800d82001b02003600, 0x1b4280368201bcca00a92406f1c803610006c1800d82001b02003600, 0xa742814e8203bcc40779280a71d014e10029c180538200a702014e00, 0x4d1a009a280011d002610004c1800982001302002600, 0x6f4280de8201bcc403792806f1d00de1001bc1803782006f0200de00, 0x5d2a00ba4800125002e10005c1800b82001702002e00, 0x6f4280de8201bcc403792806f1d00de1001bc1803782006f0200de00, 0x3d3a007a6800131001e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x1e06, 0x1e06, 0x1e02, 0x1e02, 0x6d04037a0410040001e10003c1800782000f02001e00, 0x6d04037a0411040001e10003c1800782000f02001e00, 0x1e06, 0x1e06, 0x1e02, 0x1e02, 0x6d04037a0412040001e10003c1800782000f02001e00, 0x1e0a, 0x1e0a, 0x1e02, 0x1e02, 0x1e0a, 0x1e0a, 0x1e06, 0x0, 0x0, 0x0, 0x0, 0x1e0a, 0x1e0a, 0x0, 0x0, 0x0, 0x1e0a, 0x799280f11d006a1000d41801a82003502006a00, 0x7b9280f51d00ca100194180328200650200ca00, 0x1403600420e, 0x2fa0405730803e5500d49a0038f40071d000e10001c1800382000702000e00, 0x1501c004206, 0x4206, 0x4202, 0x4610008c1801182002302004600, 0x4610008c1801182002302004600, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x4f9880f91d00721000e41801c82003902007200, 0x589880db1d00c2100184180308200610200c200, 0xda0401d368072650124920038f40071d000e10001c1800382000702000e00, 0x1603a00460a, 0x460a, 0x17024004602, 0x4602, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x54a080d71d002610004c1800982001302002600, 0x54a080d91d003a1000741800e82001d02003a00, 0x9a34013428032610054920008f40011d00021000041800082000102000200, 0x1804a001e0a, 0x1e0a, 0x1e02, 0x19024001e02, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1e0a, 0x5098809525009a1001341802682004d02009a00, 0x2b98804925004610008c1801182002302004600, 0xda0400f3a809a6500349a00692802f1c801a1000341800682000d02001a00, 0x1a03a001e0a, 0x1b030001e02, 0x1e02, 0x1e10003c1800782000f02001e00, 0x1e10003c1800782000f02001e00, 0x2fa0804125002e10005c1800b82001702002e00, 0x2fa0801525001e10003c1800782000f02001e00, 0xba540174280326100049a0009280111c80021000041800082000102000200, 0x1c04a001e0a, 0x1e02, 0x1d030001e02, 0x0, 0x0, 0x0, 0x0, 0xda0801931001e10003c1800782000f02001e00, 0xda0801931001e10003c1800782000f02001e00, 0x7a7400f428002650004c400a9240111c80021000041800082000102000200, 0x1e042001e02, 0x1f040001e02, 0x0, 0x0, 0x0, 0x0],
  [0x3d3e007a6c00f4b801e93003d1e00ea2c00f43803683003cee0079cc02337803a6b003cce00c98c0212b803e53005c9e00a92c0131f80223b003c2602804800f08800010005c1e02003800f0680000c003c1601802800f04800008003c0e01001801d02800004003c0600800800100800000, 0x3d5a00daa400f42803281005cca00a9840132680224900046c0008d40001a0002320004620000c00010a00021000041800082000f01000200, 0x480480100801000e00401800782c0000500200801c00c00801006001002000, 0x1ec5003d82007a7400f4c801e76003ce400e9b801d35001e66003cc400785000f0800020e003c1800782000f02001e00, 0x7af40235c8022b1008d2a007a4401144804275003ce20149a401d2b0022550000a80089480012700224d0000980089280251f00d23d0280780088500110800220c003c1400882001102002200, 0xf568026aa004d520682a000f4280268200750206020000f32802662007cc20581800252900d2510280a000993401325003a490000900098f40131d0002390000700098500130800260c004c1000981000f01002600, 0x7b1401560802ab9003d3a00aa6401548801e760054ea0001d001539007a6e003cd4000998015328000640054c40229480412700d64d03809800a85001508001e0e00541800a82001502002a00, 0xf56802eaa005d520882a000f42802e82003d020802000413500d6690380d000b99401731001e610000c000793401725003e4903c09000b8f40171d00023900007000b85001708002e0c005c1000b81000f01002e00, 0x7b34019648032c1003d3c00ca740004e00329a003d2c00aa4801d47001e8a00050c00ca14000420032820064e40299a80193300da650480c800c85000f0900321000641800c82001902003200, 0xf56801eaa003d520a82a00194500da89048110007a1400f41001e8100010000799400f31001e610500c000793400f25003a4904c0900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x7b3801b668000cc006d94007b1801961002ebe005574009ad8023590002ae006d5a0002b001b5500369a006d2402da2801b4300de8505810800785801b0a003610006c1800d82001b02003600, 0x1b5900deb1058160007ab400f55001ea9000150007a1400f41001e8106410000799400f31001e610600c000793400f25003a4905c0900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x3d6a00eac402346803a890084da00f9a401d23003a4500008800e90801d20800040004c7c0088e801d0a003a1000741800781801d02003a00, 0xe00480200803600e00801800782c0000500400806800c01001006001004000, 0x1ec5003d82007a7400f4c801e76003ce40079b800f3500026600f4c400785000f08003a0e003c1800782000f02001e00, 0xf62803ec1003d3a028a6400f3b003e750000e800f9c801d37003e6d0000d800f9a803533001e6201c4ac0109541d02a008a4a00a47400f85001f08001e0e007c1800f82001f02003e00, 0x3d5a011aa402342801e8101c4e40109c41d0380042650084c40079840003000424d00849400e92400024001e3d0024720108500210800420c00841001081000f01004200, 0xf66803ac9003d3c00ea740004e003a9a003d2c028a4801d47003a8d00011800ea2803943001e820074dc0119b41e03600a66200447400e85001709003a1000741800e82001d02003a00, 0x3d6a011ac401d49004691078120011a3402345001e890001100119b400f34804655008ca400e94400028001e3e002c740118500230800460c008c1000781802302004600, 0xf67003acd00019800eb2802363003ac2008d7c00fae801d5b003ab500016800eac8013570046aa00751c007a341f04600b68200447400785801d0a003a1000741800e82001d02003a00, 0x7574007ae41f05c001eb5003d64007ac400058001e8d003d120079b400f34801e55003ca400e94400028001e3e00047400785000f08001e0c003c1000781800f02001e00, 0x3d7a007ae400f4a801e91003cbc0079740002e001e5a003cb20001600212b003e52005c9c00a92800f0a001e10003c1400782000f02001e00, 0x1080480300804000e00c01800782c0000500600806800c01801007001006000, 0x1ebd003d72007a5400f48801e75003ce200e9580212900024e00849400785000f08001e0c003c1400782000f02001e00, 0xf66801ec9003d3c007a740004e001e9a003d2c007a540004a001e9200751c028a2804d43002a82003cec0079d42203a00326200549400785000f09001e10003c1800782000f02001e00, 0x3d7a007ae400f4d001e99088130007a5400f49001e910001200079d400f39001e710000e001195801d29001e4e002c9400785000f08001e0c019c1400782000f02001e00, 0xf67001ecd000198007b2800f63001ec2003d7c007af40005e001eba01856c00fac801757002aaa003d2c007a542304a00368200549400785800f0a001e10003c1800782000f02001e00, 0x3d84007b0423060001ebd003d74007ae40005c001e95003d220079d400f39001e710000e000795801d29001e4e00049400785000f08001e0c003c1400782000f02001e00, 0x3d8a007b0400f3f001e7d0000f80079e800f3c800078003cec0079c802337003a6a003ccc00c98800f0a002e0e003c1800782000f02001e00, 0x1200480400804000e0100180d80280400401000601000800b80c00001008000, 0x1ead005d52007a1400f40802e65003cc20099340232480023d008c7200b85001708002e0c005c1000b81000f01002e00, 0xf67001ecd000198007b2800f63001ec5000188007b0800f5f001eba00756c00eac800f570032aa003d3c007a742504e0036820064c400b85800f0a001e10003c1800782000f02001e00, 0x3d94007b2425064001ec5003d84007b0400060001e9d003d34007a640004c001e76003ce40079b801d35001e660004c400785000f08001e0e003c1800782000f02001e00, 0x3d4c007a9400052001ea2003d4200028000f4f001e9a003d2c007a4800f47003a8a003d0c00da0800f09001e10003c1800782000f02001e00, 0x1200480500804200e0140180e00280500401200601400800780c0000100a000, 0x1ead003d52007a1400f40801e65003cc200e93400f2480023d003c7200785000f08001e0c003c1000781000f01001e00, 0x100d00201800020e, 0x180d00301800020e, 0x2011004020000202, 0x2811005020000202, 0x80d001018003a0e, 0x2800900c01009c01c0300300200500c00800400c0300102600100c000, 0x1e0e, 0x40d80081902901e003e0a, 0xa40a00081200101c00420e, 0x40e80081902a026003a0a, 0xa80d00081800101c003a0e, 0x41380082102b032003a0a, 0xac1100082000101c00460e, 0x41980082b02c042003a0a, 0xb01600082a00101c001e0e, 0x811001020001e0e, 0x2e00900e0100b401c0380300300500e00800400c0380102600100e000, 0x1e0e, 0x40e80081b02f02a001e0a, 0xbc0e00081a001028001e0e, 0x413800823030036001e0a, 0xc012000822001028001e0e, 0x41980082d031046001e0a, 0xc41700082c001028001e0e, 0x81700102c001e0a, 0x41380082503203a001e0a, 0xc813000824001038001e0e, 0x41980082f03304a001e0a, 0xcc1800082e001038001e0e, 0x81f00103c001e0a, 0x3400901001001001c0400302d00501000809c00c04001001001010000, 0x2e0e, 0x41980083103504e001e0a, 0xd41900083000104c001e0a, 0x829001050001e0a, 0x3400901201001401c0480302e0050120080a000c04801001001012000, 0x1e0e, 0x101e00220e, 0x700a80dc1001b01200101c00260e, 0x102a002a0e, 0x760a80e81000081203901c002e0e, 0x7b3800f668000cc003d94007b1800f628000c4003d84007af800f5e8000bc003d7400ead800f5a8000b4003d64000ab800f568000ac003d5400785800f0a001e10003c1800782000f02001e00, 0x10660020c40041780082d001056001e0a, 0x7ab400f55001ea9000150007a1400f41001e8100010000799400f31001e610000c000793400f25003a490000900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x10540020800040c00081200101c001e0e, 0x104e00320a, 0x7c0a80041001e81203c01c001e0e, 0x106600360a, 0x20a81041002001203f01c001e0e, 0x1e0a, 0x3d8a00eb0400f4e803a99003cec00f9c801d37003a6d0000d800e9a801333001e6200447400e85001d0800020e00741800e82001d02003a00, 0xeae400f5a8046b1007522011a3400f44803e710084da0079a401d2a803a520074a200014001327001e3e00447400e85001d08003a0c00741001e81801d02003a00, 0x1e0a, 0x3d8a007b0400f4e801e99003cec0079d40003a001e720074dc00f9a801733001e6200549400785000f0800020e003c1800782000f02001e00, 0x7b0400f5e801eb9003d32007a5400f48801e75003ce40079c400038003e6a005ccc01095801d29001e4e00549400785000f08001e0c00841400782000f02001e00, 0x3d9a007b2400f4f001e9d000138007a6800f4b001e9200751c00ea2800f43001e820064c400785000109001e10003c1800782000f02001e00, 0x7b2400f62801ec1003d3a007a6800f4c800098003d2400ea2800f43001e76003ce40119b801d35001e660064c400785000f0800460e003c1800782000f02001e00, 0x3d9c007b3400066001eca003d8c007b0800f5f001eba00756c00eac800f57001eaa006d0400085800f0a001e10003c1800782000f02001e00, 0x7b2800f62801ec2003d8200030000f5d003ab2003d5c007a7400f4c801e76003ce40079b801d35001e66006cc400785000f08001e0e003c1800782000f02001e00, 0x1e02, 0x1e02, 0xea9f01d53603aa5c0754980ea8f01d51603aa1c07b4188a08201d4ee03a9cc0753780ea6b01d4ce03c98c4403100ea5701d4a603a93c0772588604a01cc7e0500f40751d81403a01d4262480480750881401001d41e2400380750681400c01f4162380280750481400801d40e2300180750281400401d40621000807300814000, 0x1d56a040ac402555004aa913015003aa3407f44804a8200450225820007f3680ea690094c40149844a030004a550094a403a9440a028004a4d0094940398f80251e81403c00947401285002508004a0c00941003a81802502004a00, 0x755a80d2b101ed5403aa340694480f28201d4da0349a40773100d25501a4a403a9440a02800d24d01a4940398f80691e81403c01a4740348500690800d20c01a4100128180690200d200, 0x201e00220e, 0x2960805a9900a4ea0149c802937003e6d03c0d80419980853289a06400a4ac0109544e02a000e4a00a47a0148e80290a00521000a41801482002902005200, 0x116480229d004534016a4801147003a8d04c118043a180694289e0840044dc0119b450036000e6200447a0088e80110a00221000441800882001102002200, 0x11668022ca004584014ae80115b003ab505c168012ab8069568a20ac00451c007a345204600068200447a0088e80110a00221000441800882001102002200, 0xf5e801eb9003d2a007a4400f3a801e71003cac00e94800f27007a4a11807800785000f08001e0c00441400782000f02001e00, 0x7b3800f668a80cc003d94007b1800f628a60c4003d84007af800f5e8000bc003d7400ead800f5a8000b4003d64000ab800f568000ac003d5400785800f0a001e10003c1800782000f02001e00, 0x10b1400f568046a900853a011a1400f40803e720084e22701c0045350042650084c40079840003000424d00849400f9240f024002e3d0024720108500210800420c00841001081000f01004200, 0x7b3800f668ac0cc003d94007b1800f628000c4003d84007af800f5e8aa0bc003d7400ead800f5a8000b4003d64000ab800f568000ac003d5400785800f0a001e10003c1800782000f02001e00, 0x11b3400f5e8046b9008d3c011a5402349001e9100012000ea28023448a0088014d040119d400f388046560074a401194413028001e4e002c940118500230800460c003c1401182002302004600, 0x7b38023668000cc008d94011b18023628b00c4003d84011af80235e8ae0bc003d7400ead80235a8000b4008d64000ab8023568000ac008d540078580230a004610008c1801182002302004600, 0x7b3800f63001ebd003d74007ae40005c003ab2003d622902c005b55001e95003d220079d400f38801e560074a400794417028001e4e00049400785000f08001e0c003c1400782000f02001e00, 0xc0d80181904701e00220a, 0x100e80201b04802a002202, 0x140e80281b04902a002202, 0x3d9c007b345b066001ec9003d3c007a745a04e001e9a003d2c007a545904a001e9200751c007a2800143001e8210807000785001309001e10003c1800782000f02001e00, 0x269f004d36009a5c01f4980268f004d16009a1c03b418072770144e60099bc0133580726700dcc601e95c01f29806a4f0114960098fc0251d89403a004c262f804801308816010004c1e2f00380130681600c004c162e802801f0481600800f40e2e001801302816004004c061b000800300816000, 0x13568026aa004d523082a001342802682004d0230020001332802662007cc20581800252900ee5110c0a00099340132500264902c0900098f40131d00063902c0700098500130800260c004c1000981001301002600, 0x7b1401f608026bd007d72007a740514c8072950145220079d801f3a800074007ce400f9c40b038007a6e007cd401a99801531007a56007ca400f9380452500523a007c2800f84000f07003e0c004c1400f82001f02003e00, 0x7ab400f55001ea918c150007a1400f41001e8118810000799400f31001e610000c000793400f25003a490000900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x3a9f00753600ea5c03149803a8f00751600ea1c03b4180727700fce600e9bc01d35807267014cc601e95c03129806a4f00cc960098fc0111d89603a00742633804801d0881801000741e33003801d0681800c0074163280280310481800800740e32001801d028180040074061b800800300818000, 0x1d568026aa004d523402a00134280268200750206020001d3280266200c4c23001800252900f2511100a000993401325003a490300900098f40131d0006390300700098500130800260c004c1000981001d01002600, 0x7b3401d64803ac5007582007a7801d4e80009c00753400ea640c04c001e9601452400ea3801d4500728600650401c9d803f39003a6e0074d400e9980533100223a00742800b84801d0800260e00741800e82001d02003a00, 0x7ab400f55001ea91a8150007a1400f41001e8100010000799400f31001e611a40c000793400f25003a490000900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x269f004d36009a5c0314980268f004d16009a1c05b4180c27700fce60099bc0133580c26700dcc601e95c0312980ca4f00cc960098fc0251d89803a004c263700480130881a010004c1e3680380130681a00c004c163600280310481a00801840e3580180130281a004004c061c00080030081a000, 0x13568026aa004d520682a001342802682004d023402000133280266200c4c23081800252900f6511140a0009934013250026490340900098f40131d0006390340700098500130800260c004c1000981001301002600, 0x7b38013668000cc004d94009b240d064001ec6007584007af801f5d0026b6007564009ab801b5500269e004d34009a580314900268e004d14009a1805b41004a3a003c2c00985001309002610004c1800982001302002600, 0x7ab400f55001ea9000150007a1400f41001e811c010000799400f31001e611bc0c000793400f25003a490000900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0xd60a81901002e01200201c00260e, 0x3602a0650400e206011c0a00181200301c00260e, 0x3682a05e0400900700100c00201207201c002606, 0x3382c05f0440920700140d00281407301c002602, 0xd69f01ad36035a5c06b4980d68f022d16035a1c06b418ee08201acee0359cc06b3781166b01acce03598c7603101165701aca603593c0e02680d64b0380940358fc0891d8ea03a01ac263d804806b0881c01001ac1e3d003806b0681c00c01ac163c802806b0481c00801ac0e3c001808b0281c00401ac063a000806b0081c000, 0x1ad6a020ac4041550082a91f8150035a3408f448082820055023e82000413680826a01acd20701a0041328082620234aa03594404125008a491f00900358f80411e81c03c0104740208500410800820c01041003581804102008200, 0x6b5e80d6b901ad54035a5406b4880d68201acea0359c806b3881c07001acca03598806b2b01125201ac9c0359340e02600d64a01ac7403585006b0800d60c01041403582006b0200d600, 0x80d80101907801e002a0a, 0x4560808e990114ec00f9d40b03a008a6d0114d4048998093328fe06401c4ac0229548002a008a4d0114940038e80450a008a1001141802282004502008a00, 0xaaf400f5680c2a901252a011a1401d4080e272007ce24001c002132807a62007cc205818002929007a4d00f49400e9240002400263d00247201e85003d08007a0c00f41001e81000f01007a00, 0x3032002a0a, 0x1564802a9d00553400aa5800f4a828094011d1404aa1806b429020840054ec0079d48203a001a6200549a00a9280150a002a1000541800a82001502002a00, 0x1566802aca00558400aaf800f5e8300bc011564020ab806b569060ac00552c007a548404a000a8200549a00a9280150a002a1000541800a82001502002a00, 0xf5a801eb1003d1a007a2400f36801e691e40c800795401d28801e3e00847400785000f08001e0c003c1000a81800f02001e00, 0x7b380156690c0cc005594007b18015628000c4005584007af80155e8000bc00557400ead80155a90a0b4003d64000ab8015568000ac0055540078580150a002a1000541800a82001502002a00, 0x7b3400f62801ec1003d3a007a6800f4c800098003d24007a448204800468e0065040079d800f39001e710500e00119b801d35001e66002cc400785000f08002e0e003c1800782000f02001e00, 0x7b38015668000cc005594007b18015629100c4005584007af80155e8000bc005574030ad80155a90e0b4003d64000ab8015568000ac0055540078580150a002a1000541800a82001502002a00, 0x7b3800f62801ec2003d8200030000f5d001eb9210170007ad801b55001e9d003d320079d800f39001e710600e00079b801d35001e660004c400785000f08001e0e003c1800782000f02001e00, 0x101380202307a036002a02, 0x141380282307b036002a02, 0x3d9c007b348b066001ec9003d3c007a748a04e001e9a003d2c007a4801d47001e8d224118007a2800143001e821d009000785001709001e10003c1800782000f02001e00, 0x2e9f005d3600ba5c01749802e8f007d1600ba1c04f41802e77005ce60269bc05135809a67012cc601095c01f29802e4f0104963e01280351f80523b005c264780480170881e010005c1e4700380170681e00c0084164680280170481e008005c0e46001801f0281e004005c061c80080050081e000, 0x1756802eaa005d524882a001742802e82005d024802000413500d6691d40d000b99401731002e6103c0c000b93401725003e4903c09000b8f40171d000a3903c07000b85001708002e0c005c1000b81001701002e00, 0x7af401f5c802eb5007d62011a5405148809a8d0145120109d401f3880426d007cd202298801d2b003e550000a800f94801f2881e05000d49c0089280311f00523a007c2800f84001f06001e0a007c1000b81801f02003e00, 0x1e9f003d36007a5c00f49801e8f007d16007a1c04f41801e77003ce60269bc05135809a670064c601095c01f29802e4f0054963e81280351f80523b003c264a804800f08820010003c1e4a003800f0682000c003c1649802800f04820008003c0e49001801f02820004003c061d000800500820000, 0xf56802eaa005d524b02a001742802e82003d020802000413500d6691d80d000b99401731001e610400c000793401725003e4924009000b8f40171d000a3904007000b85001708002e0c005c1000b81000f01002e00, 0x7b3400f64801ec5003d82007a7800f4e80009c003d34007a641004c001e96003d24011a3805145009a860065040079d800f39009a6e0144d400799801931002a4a003c2800784800f08002e0e003c1800782000f02001e00, 0x7ab400f55001ea9260150007a1400f41001e8100010000799400f31001e610000c000793400f25003a4925c0900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x2e9f005d3600ba5c01749802e8f007d1600ba1c01b41802e77005ce60119bc05135804667012cc601095c01f29802e4f0104963f01280351f80523b005c264e004801708822010005c1e4d80380170682200c008c164d002801704822008005c0e4c801801f02822004005c061d800800500822000, 0x1756802eaa005d520882a001742802e82005d024b02000413500d6691dc0d000b99401731002e610440c000b93401725003e4924409000b8f40171d000a3904407000b85001708002e0c005c1000b81001701002e00, 0x7b38017668000cc005d9400bb2411064001ec6003d8400baf800f5d001eb6007d6400bab801b55002e9e005d3400ba5801749002e8e007d1400ba1801b4100824a003c2c00b85001709002e10005c1800b82001702002e00, 0x7ab400f55001ea9000150007a1400f41001e8127810000799400f31001e610000c000793400f25003a492740900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x4c82a09204013e0601e00a00101200201c002e0e, 0x1340a824c1004681200301c002e0e, 0x4d82a07a0480080802380c0020120a001c002e06, 0x4a82c07b04800a08823c0d0028140a101c002e02, 0xda9f01b536036a5c06d4980da8f025d16036a1c06d4194a08201b4ee0369cc0973780da6b01b4ce09019406d3182406201b4ae04c94c06d2780da4b2900940368fc0971d94603a01b42654804806d0882401001b41e54003806d0682400c01b41653802806d0482400801b40e5300180970282400401b40651000806d00824000, 0x1b56a00cac4019550032a92b015000ca340194500da8904811000ca140194100da6d0274d200c98801930956060026caa0369440192500a6492a80900368f80191e82403c00647400c8500190800320c00641003681801902003200, 0x6d6280dac101b554036a7406d4d00da99048130036a1406d4100da7601b4e40369b80973500da6601b4ca09019006d3100da4a01b47403685006d0800320e01b41803682006d0200da00, 0x8138010210a603200320a, 0x536480a69e00753a0602700554900a68d014d1404fa1809b4295a0840074dc0299b4ae03600a665014cc40038e80530a00a610014c180298200530200a600, 0xcaf400f5a803ab100752400ea44ae04800468d00751400ea240c04400ae75008cda00f9a401d2a803a520074a20001400112500263e002c7400e85001d08003a0c00741000781801d02003a00, 0xc138018210a703200320a, 0x196480329e003d3a0802700194a803292015514050a1806d4295e084003cec00c9d4b003a0032650064c40069280190a00321000641800c82001902003200, 0x7b1400f5e801eb9003d34007a64b004c001e95003d24007a4410048001e75003ce40079c40003800426e0054c401195801f29002e4e002c9400785000f08001e0c003c1400782000f02001e00, 0x4046003202, 0x19668032ca00658c007b14190620032ba014d6400cab806d569620ac00653c007a74b204e0002820064ca00c9880190a00321000641800c82001902003200, 0xf56801ea92a0118007a1400f40801e65003cc200793401d24801e3d008c7200785000f08001e0c003c1000781001901001e00, 0x7b38019668000cc006594007b18019628000c4006584007af80195e9680bc00557400ead80195a9660b4003d64000ab8019568000ac0065540078580190a00321000641800c82001902003200, 0x7b3400f65001ec9000190007b0800f609640c0003d7c007ad801b55001e9e003d34007a641904c001e96003d24007a3801d45001e8600050400785000f09001e10003c1800782000f02001e00, 0x141980282d0a9046003202, 0x3d8c007b14b7062001ec1003d3a007a64a2040001e76003cea5b01d000f39003a6e003cda5a81b000f35000266003cc400785000f08001e0e003c1800782000f02001e00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b41801e77003ce60119bc01d35801e670064c65501880592b80a25301349e00a92c0391f80223b003c265d804800f08826010008c1e5d003800f0682600c003c165c802800f04826008003c0e5c001801d02826004003c061e000800100826000, 0xf56801eaa003d525e82a00194500da8928c110007a1400f41001e8104c10000799400f31001e612f00c000793400f25003a4904c0900078f400f1d00023904c07000785000f08001e0c003c1000781000f01001e00, 0x7af401d5c801eb5007562011a5401d4880468d007512029a080213a80a2710164da0289a401d2b003a550000a800e94801d2882605000e49c0089280131f00223a00742800e84001d06001e0a00741000781801d02003a00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b41801e77003ce60119bc01d35801e670064c65581880592b80a25301349e00a92c0391f80223b003c2660804800f08828010005c1e60003800f0682800c003c165f802800f04828008003c0e5f001801d02828004003c061e800800100828000, 0xf56801eaa003d526102a00194500da89290110007a1400f41001e8105010000799400f31001e610500c000793400f25003a492f00900078f400f1d00023905007000785000f08001e0c003c1000781000f01001e00, 0x7b1400f60801ebd003d72007a7400f4c801e95003d2200ca0800f3b001e750000e80079c800f388280700084dc0289a804d33002a620164ac02894801727002a4a003c2800784000f07001e0c003c1400782000f02001e00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b41801e77003ce60119bc01d35801e670064c65601880212b80a25301349e00a92c0391f80223b003c2663004800f0882a010008c1e62803800f0682a00c003c1662002800f0482a008003c0e61801801d0282a004003c061f00080010082a000, 0xf56801eaa003d520a82a00194500da89294110007a1400f41001e8105410000799400f31001e613080c000793400f25003a492f40900078f400f1d00023905407000785000f08001e0c003c1000781000f01001e00, 0x7b3800f668000cc003d94007b2415064001ec6003d84007af800f5d001eb6007564007ab801b55001e9e003d34007a5800f49001e8e007514007a1801b41003262003c2c00785000f09001e10003c1800782000f02001e00, 0x7ab400f55001ea9000150007a1400f41001e8100010000799400f31001e613200c000793400f25003a4931c0900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0x6182a0a60440040803240c05f01200201c001e0e, 0x6202a0a70440060803280c05c81200301c001e0e, 0x18a0b03001105d01a004028001e02, 0x5482e0050581820882ec0d0028140cb01c001e02, 0xde9f01bd36037a5c06f4981468f01bd16037a1c1604280de830581040379dc06f3980de6f028cd603799c06f3199e06201bcae05294c06f2780de4b3380940378fc0a31d99a03a01bc2669804806f0882c01001bc1e69003806f0682c00c01bc1668802806f0482c00801bc0e6800180a30282c00401bc0666000806f0082c000, 0x6d6a00dac806f5882c0b0006d5a00daa806f46803289006d0400da04d604000de6d0054d200d98801b309aa060029caa03794401b2500b6493500900378f801b1e82c03c006c7400d85001b0800360c006c1003781801b02003600, 0x6f6680deca01bd920b032006f5680deaa01bd3c037a6806f4b00de9201bd1c051a2806f4300de85058108037a0806f3100de4a01bc7403785000f0900de1001bc1803782006f0200de00, 0x81980102b0d004200360a, 0x5b670026cd03419802db0805d5d00b6b5016d64054ab80a7569ae0ac004d1c02da34d804600b685016d040018e805b0a00b610016c1802d82005b0200b600, 0x9ae80135c9b00b8003d6a009ac80135881a0b0006d2a007a3401d4480be75003cda00f9a40132a8026520074a20001400252500263e0004740098500130800260c004c1000781801302002600, 0xc1980182b0d104200360a, 0x1b67002ecd04419800db0801b5e8036ba01756402fab806f569b20ac005d2c00da54da04a003685006d0400292801b0a003610006c1800d82001b02003600, 0xbb08017609b40c0003d7a00bae80175c8220b8005d3a007a5400f48802e75005ce40079c40003800426e0104c400795801f29002e4e00049400b85001708002e0c003c1400b82001702002e00, 0x101980202d0d2046003602, 0x1b67001ecd05419800db1401b610036ba016d6400dab806f569b60ac003d3c055a74dc04e003685006d0400098801b0a003610006c1800d82001b02003600, 0x7b2800f649b80c8003d8a007b0800f6082a0c0003d3a007a6800f4c800098003d2c011a3801941001e76003ce40079b801d35001e660004c400785000f08001e0e003c1800782000f02001e00, 0x505a003602, 0xd305a001ead003d52007a1400f40801e65003cc201193401d24801e3d003c7200785000f08001e0c003c1000781001b01001e00, 0x3d8a007b04cc054001e9e003d3a6f827000f4c801e76003cea6f01d000f39003a6e003cda6e81b000f35000266003cc400785000f08001e0e003c1800782000f02001e00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b419a8082003cee0079cc02337803a6b003cce00c98c0212b803e53005c9e00a92c0131f80223b003c2671804800f0882e010005c1e71003800f0682e00c003c1670802800f0482e008003c0e70001801d0282e004003c061f80080010082e000, 0x1b5900deb1334160007ab400f55001ea905c150007a1400f41001e8139410000799400f31001e613900c000793400f25003a4905c0900078f400f1d00023905c07000785000f08001e0c003c1000781000f01001e00, 0x7af401d5c801eb500756202daa80234a803a91008d1a00ea240213a803e710084da00f9a401d2b003a550000a800e94801d2882e050004c9c0089280131f00223a00742800e84001d06001e0a00741000781801d02003a00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b419aa082003cee0079cc02337803a6b003cce00c98c0212b803e53005c9e00a92c0131f80223b003c2674804800f08830010005c1e74003800f0683000c003c1673802800f04830008003c0e73001801d02830004003c0620000800100830000, 0x1b5900deb1338160007ab400f55001ea9060150007a1400f41001e813a810000799400f31001e610600c000793400f25003a493900900078f400f1d00023906007000785000f08001e0c003c1000781000f01001e00, 0x7b1400f60801ebd003d7200daa800f4e801e99003d2a007a4400f3b001e750000e80079c800f388300700084dc00f9a801733002a620084ac00f94801727002a4a003c2800784000f07001e0c003c1400782000f02001e00, 0x1e9f003d36007a5c00f49801e8f007516007a1c01b419ac082003cee0079cc02337803a6b003cce00c98c0212b803e53005c9e00a92c0131f80223b003c2677004800f08832010005c1e76803800f0683200c003c1676002800f04832008003c0e75801801d02832004003c0620800800100832000, 0x1b5900deb133c160007ab400f55001ea9064150007a1400f41001e8106410000799400f31001e613a80c000793400f25003a493940900078f400f1d00023906407000785000f08001e0c003c1000781000f01001e00, 0x7b3400f64801ec5003d8200daa800f4f001e9d000138007a6800f4c832098003d2c007a4802347003a8a003d0c00ca0800f3b001e72008cdc00e9a800f33003262003c2800b84800f08002e0e003c1800782000f02001e00, 0x6802c0020541d60803bc0c07301200201c001e0e, 0x6882c0030541d80803c00c07081200301c001e0e, 0x6902e0040581d00883880d0020140f101c001e02, 0x1dc0b03a41107181a005028001e02, 0x1811003020003a0e, 0x201700402c003a02, 0x281700502c003a02, 0x80e8010190f2026007a0a, 0x3c80d00101800201c00020e, 0x1011002020001e0e, 0xf40090340103cc01c0d00300300503400800800c0d001026001034000, 0x1e0e, 0x80e80101b0f502a001e0a, 0x3d40e00101a002028001e0e, 0x8138010230f6036001e0a, 0x3d812001022002028001e0e, 0x81980102d0f7046001e0a, 0x3dc1700102c002028001e0e, 0x101700202c001e0a, 0x8138010250f803a001e0a, 0x3e013001024002038001e0e, 0x81980102f0f904a001e0a, 0x3e41800102e002038001e0e, 0x101f00203c001e0a, 0xfa00903601001001c0d8030f300503600809c00c0d801002001036000, 0x2e0e, 0x8198010310fb04e001e0a, 0x3ec1900103000204c001e0a, 0x1029002050001e0a, 0xfa00903801001401c0e0030f40050380080a000c0e001002001038000, 0x1e0e, 0x3d8a056b0400f4e803299003cec00a9c801337001e6a0004cc01e99400032007a6200447201e85003d08003a0e00f41801e82003d02007a00, 0x3d5a011aa400f42801e81005cca0079840132a801e4d0044920008f40011d0002390000700008500010800020c00041000081001d01000200, 0x2036003e0a, 0x202400420e, 0x20660040c40081780102d002056001e0a, 0x20540040800080c00101200201c001e0e, 0x204e003a0a, 0x204400460e, 0x2066003a0a, 0x2058001e0e, 0x1e0a, 0x3d8a007b0400f4e801e99003cec0079d40003a001e720084dc0079a800133002a6200f4a400785000f08003a0e003c1800782000f02001e00, 0x1ebd003d72007a5400f48801e75003ce40079c40003800426e0054c400795801f29002e4e02bc9400785000f08001e0c00841400782000f02001e00, 0x3d9a007b2400f4f001e9d000138007a6800f4b001e92008d1c007a28001430032820074d400785001309001e10003c1800782000f02001e00, 0x1ec5003d82007a7400f4d001e99000130011a3801941001e76003ce40079b801d35001e6602c4c400785000f0800460e003c1800782000f02001e00, 0x3d9c007b3400066001eca003d8c007b0800f5f001eba003d6c007ac800157015aaa00751400e85800f0a001e10003c1800782000f02001e00, 0x1ec5003d84007b0400060001eb6006d54007a7400f4c801e76003ce40079b801d35001e6602a4c400785000f08001e0e003c1800782000f02001e00, 0x1e02, 0x1e02, 0x1ead00d554032aa4fd054001e8500d504059a04fc04001226a024cd23f81a001732806a62007cc205818008329010a511340a000993403525003e4903c09001a8f40351d00023900007001a85003508006a0c00d41001a81000f01006a00, 0x10a7c0214d803e97007d26010a3c05f458042870085060289dc0513980b26f015cd601099c02131806a5700a4a601093c1d026803e4b0740940108fc0091d9fe0390164268100480210883a01000841e8080380210683a00c00841680002801f0483a00800840e1480180070283a0040084067f00080210083a000, 0x2dd7a05aae40b74a816a9101c4ea0389c801f3883a07001c4ca0389880b52b00525200849c0389341d02600e24a001c720388500710800e20c0084140388200710200e200, 0x857a010ae40214a8042910084ea0109c801f3883a0700084ca0109880212b008a5200849c0109341d02600424a02e4720108500210800420c00841401082002102004200, 0x3036003e0a, 0xf56801ea9003d0a007a050003a001e65003cc200793402124801e3d00047200785000f08001e0c003c1000781001f01001e00, 0xf66800ec9003d3c028a740004e00a29a003d2c028a540004a00a29200751c028a340004600a28a001d0c007a0805531008e4a00b47402885000f0900a2100144180288200510200a200, 0x7b2400f62801ec1003d3a007a6800f4c800098003d2400ea2800f43001e76003ce40119b801d35001e660064c400785000f0800ce0e003c1800782000f02001e00, 0xf67003ecd00019800fb2800f63000ec2003d7c00faf40005e003eba00756c00fad40005a003eb2001d5c007aa805d41008a4a00a47400785801f0a003e10007c1800f82001f02003e00, 0x7b2800f62801ec2003d8200030000f5d003ab2003d5c007a7400f4c801e76003ce40079b801d35001e66006cc400785000f08001e0e003c1800782000f02001e00, 0x101380202510103a003e02, 0x7e0800fbf000f7a000ef00195d8032b9001f66001ec4003d380079d000f36004254, 0x141380282510203a003e02, 0xf66801ec9003d3c007a6800f4b001e9200751c007a2800143001e823f80a000785002109001e10003c1800782000f02001e00, 0xf5a8092b1017d52011a340154480ae81001ce405c9c4ff03800426d0054d203599403d2a80225101dc9a0008f80091e80003c0024740048500090800120c00241000781800902001200, 0x7b3400f64801ec1003d3c007a740004e001e9a003d2c007a4801d47003a8a003d0c00aa0800f3b003a6e0064c400785001709001e10003c1800782000f02001e00, 0x7ab4023550046a9410150011a1402341001e8100010001199402331001e610000c001193402325003a490000900078f40231d00163940c0700118500230800460c008c1001181000f01004600, 0x7b38023668000cc008d94011b1800f610046be003d74030ad801d59001eae012554011a680234b00c28e006d040078580230a004610008c1801182002302004600, 0x7ab400f55001ea9000150007a1400f41001e8141810000799400f31001e610000c000793400f25003a490000900078f400f1d00023941407000785000f08001e0c003c1000781000f01001e00, 0x302400420e, 0x40413002020004030004206, 0x40813002822005034004202, 0x1ead00e554030aa508054013e8a026d1256822000f4280728200750206020000f328072620144c28381800872900d25113c0a000993403925003a4904c09001c8f40391d00023900007001c8500390800720c00e41001c81000f01007200, 0xea7c01d4d804697008d26011a3c02345804687006d060289dc0513980466f0780da00e9ac1e0350072670044c601195c02329809a4f0124960118fc00b1da1203a0134268680480230883c010008c1e86003801d0683c00c008c168580280230483c008008c0e8500180230283c004008c061580080070083c000, 0x2f57a00eae401d4a803a920075220f024001d46803a8a02f4ea05d9c40232b003a550780a800e9480132700224a001c7400e85001d08003a0c008c1400e82001d02003a00, 0x8d8a011b040234e80469a0075320f02600234680468a008cec0119c80233700466d0780d80119a80233300a66202fc740118500230800460e008c1801182002302004600, 0xc1380182310b036003a0a, 0x7b0400f5e801eb9003d32007a5400f48801e75003ce40079c400038003e6a005ccc01095801d29001e4e00549400785000f08001e0c019c1400782000f02001e00, 0x7608007bf00077c00c2f40075d8030b9000f66003abc003d38007a5000f4600466c, 0x404a003a02, 0xf56802ea9430128007a1400f40802e65003cc200793402324802e3d00047200b85001708002e0c005c1000b81001d01002e00, 0xf67003acd00019800eb2800f63003ac500018800eb0800f5f000eba00756c00ead40005a003ab2001d5c007aa805b4100a66200447400b85801d0a003a1000741800e82001d02003a00, 0x7b3400f65001ec9000190007b0800f5d003ab2003d5c007a7800f4d001e96003d24007a3801d45001e86017d0400785000f09001e10003c1800782000f02001e00, 0x141980282f10d04a003a02, 0xf5e8186b9006d52011a5401948800e8a02fd1284822006d42809a750054e202498401d2b00225200049c0059340002600164a03047a00585000b0800160c003c1400582000b02001600, 0xf62801ec1003d3a007a650a044001e76003ce40099b800f35000266003cc400785000f0800460e003c1800782000f02001e00, 0x7b1400f60801eb9003d3a007a6400f4a801e76003cea0001d000f39003a6e007cd400b99801531007a5600549400785000f08001e0e003c1800782000f02001e00, 0x7b38023668000cc008d94011b1800f610046be003d7400ead801d59001eae030d54011a7802349003a8e006d040078580230a004610008c1801182002302004600, 0x7ad400f59001eb1000160007a3400f45001e890001100079b400f35001e6943c0d000795400f29003a510000a00078f80011d001e3943807000785000f08001e0c003c1000781800f02001e00, 0x42c1200182200302800460e, 0x4038004602, 0x4341800282e005038004602, 0x152b2029d626b82c000f568026aa004d520682a000f4280268200750288820000f32802662007cc28801800252900d2511440a000993401325003a4905c0900098f40131d0002390000700098500130800260c004c1000981000f01002600, 0xea7c01d4d803e97007d26007a3c1f046803a8b07c114009a1c01141801e77003ce60079bc00f35801e670064c600795c00f29802e4f0054960078fc0011da2403a003c268b004801d0883e010005c1e8a803800f0683e00c003c168a002800f0483e008003c0e89801800f0283e004003c061600080010083e000, 0x757a00eae801d5c83e0b800756a00eac80c54a803a910314ea00f9c400f2b003a5507c0a800e9480132700224a000c7400e85001d08003a0c003c1400e82001d02003a00, 0x3d9a007b2801d6483e0c8003d6a007ac800f4f001e9a003d2c007a4800f47001e8d07c118007a2800f4300b68200047400785000f09001e10003c1800782000f02001e00, 0xc1980182d114046003a0a, 0x3e08011bf00077c0046f4008dd8007b9001d66001eb400753800ea5001d4600c274, 0x11b0400f5e8046b9008d32011a5400f48804675008ce40079c400038003e6a0134cc01095801d29001e4e0124940118500230800460c003c1401182002302004600, 0x101980202f11504a003a02, 0x11b2400f628046c1008d3a011a6800f4c800098008d2400ea2802343004676003ce40119b801d35001e66015cc401185002308001e0e008c1801182002302004600, 0x505e003a02, 0x11605e001ead003d52007a1400f40801e65003cc200793400f24809a3d00047200785000f08001e0c003c1000781001d01001e00, 0xf5e8036b9000d64000ac51205800dead003d2a00ca4401940802e750054e200a9840132b00225200049c0009340002600024a031c7a0008500010800020c003c1400082000102000200, 0xf62801ec144c160007a7400f4c801e76003ce400e9b800f35000266003cc400785000f08001e0e003c1800782000f02001e00, 0x7b1400f60801ebd003d3a007a6400f48801e76003cea0001d000f3900c26e007cd400b99801531007a5600549400785000f08001e0e003c1800782000f02001e00, 0x7b3400f64801ec5003d3c007a740004e001e9a003d2c007a4801d47003a8a003d0c00ca0800f39003a6e0064c400785001709001e10003c1800782000f02001e00, 0x4501700182c003028001e0e, 0x4541800202e004038001e02, 0x5038001e02, 0x201f00403c001e02, 0x281f00503c001e02, 0xc0e80181911702600420a, 0x45c0d00181800301c00020e, 0xc0e80181b11802a00420a, 0x4600e00181a003028003a0e, 0x181700302c001e0a, 0xc1380182511903a001e0a, 0x46413001824003038001e0e, 0xc1980182f11a04a001e0a, 0x4681800182e003038001e0e, 0x181f00303c001e0a, 0x11b00904001001001c100030f30050400080b400c10001003001040000, 0x2e0e, 0xc1980183111c04e001e0a, 0x4701900183000304c001e0a, 0x1829003050001e0a, 0x11b00904201001401c108030f40050420080b800c10801003001042000, 0x1e0e, 0x3d7a011ae400f4a801e91005cea0079c401530803a560084a40009380212680004c0084940108500210800420c003c1401082002102004200, 0x3d5a056aa400f42803281005cda0079940153080264d0074920008f40011d0002390000700008500010800020c00041000081000f01000200, 0x3d7a011ae40234a801e910084ea0079c402134803a560084aa0001500212900024e0084940108500210800420c003c1401082002102004200, 0x1eb5007562007a3401d44804275003cda00f9a401d2a803a520074a20001400112500263e03247400e85001d08003a0c00741000781801d02003a00, 0x30660060c400c1780182d003056001e0a, 0x305400608000c0c00181200301c001e0e, 0x3d9a007b2400f4f001e9d000138007a6800f4b001e9200751c007a2800143001e82003ce400785001709001e10003c1800782000f02001e00, 0x1ebd003d72007a7800f4a801e92003d2200024001941001e75003ce200795801d29001e4e015c9400785000f08001e0c003c1400782000f02001e00, 0x3d9c007b3400066001eca003d8c007b0800f5f001eba00756c011ac8001570046aa003d2400785800f0a001e10003c1800782000f02001e00, 0x1ec6003d7a007ae800f5c8000b8006d54007a5400f48801e75003ce200795801d29001e4e017c9400785000f08001e0c003c1400782000f02001e00, 0x304e001e0a, 0x304c001e0a, 0x3066001e0a, 0x3060001e0a, 0x1e02, 0x1e02, 0x1ead013554011aa51e05401428a01b51257822000f42809a82003d020802000953500d6692040d000b99404d31001e610500c000793404d2500a2494740900268f404d1d00023900007002685004d08009a0c01341002681000f01009a00, 0xeae400f5a8046b1007522011a3400f44803e710084da0079a401d2a803a520074a200014001327001e3e00447400e85001d08003a0c00741000781801d02003a00, 0x7a7c00f4d801e97003d26007a3c06145801e87006d060079dc2203a801e730880e40289bc05135809a670054c601195c06129801e4f002c968f81280391f805e3b003c2691004800f08844010003c1e90803800f0684400c019c1690002800f04844008003c0e7b001806102844004003c0618000800d00844000, 0x3d8a007b0400f4e801e9a003d3211026000f4a801e92003cec0079d42203a001e720334dc0659a801733002a6200349400785000f08001e0e003c1800782000f02001e00, 0x3d8a007b0400f4e801e9a003d3211026000f4a801e92003cec0079d42203a001e72008cdc0309a800f33003262033c9400785000f08002e0e003c1800782000f02001e00, 0x404e001e02, 0xf56801ea9484138007a1400f40801e65003cc200993401d2480263d00047200785000f08001e0c003c1000781000f01001e00, 0xf67001ecd000198007b2800f63001ec5000188007b0800f5f001ebd000178007ae801d5b000eb2001d5c00aaa801b4100326200549400785800f0a001e10003c1800782000f02001e00, 0x7b3400f65001ec9000190007b0800f5d003ab2003d5c007a7800f4d001e96003d24007a3801d45001e8602a50400785000f09001e10003c1800782000f02001e00, 0x141980283112204e001e02, 0xf62815ac1006d52007a740194c801a92033d228f824009d42801e760054e401c9b800f35000266002cca00019000b31011e4d00bc7200585000b08001e0e002c1800582000b02001600, 0x7b1401d60803ab1003d3a00ea6402346801e76007ce400e9b801d3680006c0074d400999800f3100425500447400e85001d0800ce0e00741800e82001d02003a00, 0xf5e80ceb9480130007a5400f48802e75003ce200e9580232900024e008c940338500670800ce0c003c140338200670200ce00, 0x7b3800f668000cc003d94007b1800f61001ebe003d74030ad801d59001eae02b554007a7800f4b00c28a006d0403385800f0a001e10003c1800782000f02001e00, 0x7af400f5d001eb9000170007a5400f49001e910001200079d400f39001e710000e000795801d29001e514900a000793800125001e4948c09000785000f08001e0c003c1400782000f02001e00, 0x404c001e02, 0x4881900283000504c001e02, 0xbeb201bd626c82c000f56802eaa005d520882a000f42802e82003d029302000413500d66920c0d000b99401731001e610600c000793401725003e4949409000b8f40171d00023900007000b85001708002e0c005c1000b81000f01002e00, 0x30ae400f5a8046b1018522011a3400f44803e710084da0079a40612a80c2520074a200014003927001e3e00bc740308500610800c20c0184100078180610200c200, 0x7a7c00f4d801e9708c12a007a4c23049003e8f007d1600ba1c01541801e77003ce60119bc01d35801e670064c600795c01d29801e4f0004969381280131f80223b003c2695004800f08846010005c1e94803800f0684600c003c1694002800f04846008003c0e7b801801d02846004003c0618800800100846000, 0x3d8a007b0800f608460c0003d7a007ae800f4e801e99003cec0079d42303a001e720344dc00f9a801733002a6200149400785000f08001e0e003c1800782000f02001e00, 0x3d9a007b2800f648460c8003d7a007ae800f4f001e9a003d2c007a542304a001e92003d1c00ea2800f4300368200049400785000f09001e10003c1800782000f02001e00, 0x101980203112904e001e02, 0x7b2400f62801ec1003d3a007a6800f4c800098003d24030a2800f43001e76003ce40119b801d35001e6602c4c400785000f0800ce0e003c1800782000f02001e00, 0x5062001e02, 0x12a062001ead003d52007a1400f40801e65003cc200e93401d2480723d00047200785000f08001e0c003c1000781000f01001e00, 0xf628036c1001574000ae52705c001ead003d3a00ca6401940802e760054e40099b8023350002660004ca00019000131002e4d00447200085000108001e0e00041800082000102000200, 0x7b1401d60801eb5008d3a00ea6401d44804676007ce400e9b801d3680006c0074d40099980233100425500447400e85001d08001e0e00741800e82001d02003a00, 0x128060001ebd003d72007a5400f48801e75003ce200e95800f2900024e003c9400785000f08001e0c003c1400782000f02001e00, 0x7b3400f64801ec5003d3c007a740004e001e9a003d2c007a4801d47003a8a003d0c00ca0800f3b003a6a0064c400785001709001e10003c1800782000f02001e00, 0x4a41900203000404c001e02, 0x504c001e02, 0x2829005050001e02, 0x200d004018002e02, 0x100a80201312b01e004602, 0x4ac0a00201200401c000206, 0x100e80201912c026004602, 0x4b00d00201800401c002606, 0x101380202112d032001e02, 0x4b41100202000401c002e06, 0x101980202b12e042002e02, 0x4b81600202a00401c001e06, 0x2029004050001e02, 0x11b0090480103e801c1200303400504800801400c12001004001048000, 0x1e06, 0x3d6a011ac400f46801e8900650200b9b400f34802655008ca20008f80231e80003c008c740118500230800460c008c1000781802302004600, 0x3d5a069aa400f46801e8500650200b9940153080264d0044920008f40011d0002390000700008500010800020c00041000081000f01000200, 0x3d7a011ae40234a801e91008d120119d400f38803a56008caa0001500232900024e008c940118500230800460c003c1401182002302004600, 0x1ead004d52011a5400f42803a81003cca00f9840252900264d004c9400e9240002400263d00bc720098500130800260c004c1000981000f01002600, 0x3d8a007b0400f4e801e99003d220079d800f3a800074003ce40309b800f35000266003cc400785000f08001e0e003c1800782000f02001e00, 0x1ead005d5200ba7400f42801e810104d400b99401731001e610000c000793401f24802e3d01247200b85001708002e0c005c1000b81000f01002e00, 0x40660080c40101780202d004056001e02, 0x40540080800100c00201200401c001e06, 0x3d9c00bb3400066002eca003d8c007b080175f001eba004d6c011ac8001570046aa005d340078580170a002e10005c1800b82001702002e00, 0x1ece006d64007ab400f55001ea9000150007a1400f40801e65003cc200793401d24801e3d006c7200785000f08001e0c003c1000781000f01001e00, 0x4066001e02, 0x4064001e02, 0x2e02, 0x36b201bd626d82c000f56801eaa003d520a82a00194500da892c4110007a1400f41001e8106410000799400f31001e614c00c000793400f25003a494bc0900078f400f1d00023900007000785000f08001e0c003c1000781000f01001e00, 0xeae400f5a8046b1007522011a3400f4480ca710084da0079a401d2a803a520074a200014001327001e3e03247400e85001d08003a0c00741000781801d02003a00, 0x7b0400f5e801eb9003d32007a5400f48801e75003ce40079c40003800ca6a005ccc01095801d29001e4e02bc9400785000f08001e0c019c1400782000f02001e00, 0x7a7c2504e801e9b094134007a5c00f49803a8f007516007a1c01941801e77003ce60079bc01d35801e670004c69881880212b803e53005c9e00a92c0131f80223b005c2699804800f0884a010003c1e99003800f0684a00c003c168e002800f0484a008003c0e7d801801d0284a004003c061a80080010084a000, 0x3d9a007b2800f6484a0c8003d8a007b0800f4f001e9d094138007a6800f4b001e9203551c00ea2800f430032820004c400785001709001e10003c1800782000f02001e00, 0x3d9a007b2800f6484a0c8003d8a007b0800f4f001e9d094138007a6800f4b001e92003d1c00ea2800f430156820004c400785000f09001e10003c1800782000f02001e00, 0x5066001e02, 0x133066001ead005d52007a1400f40802e65003cc200993401d24806a3d00047200b85001708002e0c005c1000b81000f01002e00, 0xf668036c9000584000b0531060001ead003d3c00ca680174b002a92004d1c010a2800143000285000108000a0800f32802a4900447200085000f0900021000041800082000102000200, 0x7b3401d64801eb5008d3c00ea680214b003e9200751c00ea3400046003a8a004d0c010a0802336803e5100447400e85000f09003a1000741800e82001d02003a00, 0x7b3400f64801ebd003d3c007a6800f4b001e95000128007a4803d47003e8a005d0c00aa0800f3a803e5200549400785000f09001e10003c1800782000f02001e00, 0x132064001ead003d52007a1400f40801e65003cc200e93400f2480023d003c7200785000f08001e0c003c1000781000f01001e00, 0x5064001e02, 0x280d005018001e02, 0x140a80281313401e001e02, 0x4d00a00281200501c000206, 0x140e802819135026001e02, 0x4d40d00281800501c003a06, 0x1413802821136032001e02, 0x4d81100282000501c001e06, 0x141980282b137042001e02, 0x4dc1600282a00501c001e06, 0x3d6a007ac400f54801e8d003d120079b400f34803a55003ca20008f800f1e80003c003c7400785000f08001e0c003c1000781800f02001e00, 0x3d6a007ab401b54801e8500650200b9940153080264d0044920008f40011d0002390000700008500010800020c00041000081000f01000200, 0x3d7a007ae400f58801e95003d220079d400f38803a56003caa00015000f2900024e003c9400785000f08001e0c003c1400782000f02001e00, 0x1ebd003d5a00eaa402342803a81008cca00f98401129003a4d00749400e9240002400263d00447200e85001d08003a0c00741000e81000f01003a00, 0x3d8a007b0400f5c801e9d003d320079d800f3a800074003ce400e9b800f35000266003cc400785000f08001e0e003c1800782000f02001e00, 0x1ec5003d5a007aa400f42801e810054d400799400f31001e610000c001193401f24802e3d00547200785000f08001e0c003c1000781000f01001e00, 0x3d9a007b2400f60801e9e003d3a00027000f4d001e96003d2400ea3800f45000286003d0400785000f09001e10003c1800782000f02001e00, 0x1ecd003d5a007aa401945001e85003d04007a0400040001e65003cc201193401d24801e3d00647200785000f08001e0c003c1000781001701001e00, 0x506600a0c40141780282d005056001e02, 0x505400a0800140c00281200501c001e06],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000, 0x59e000b2c00163800ac300057e001aec001578160ad0005560502a400b4f801a9b002d2e003a4c001438120850005060402040093b800e730014ce0381940053180c061000c9e0281340032580804900046e0080d80101a8000340004660080c80101880003000042e1380580010a8020140004261300480010880201000041e1280380050680200c0004161200280030480200800040601800800100802000, 0x11413e22026c4004b87e0930ec11e1d022c320438620830f80ee1e81cc3903787006b0c00ce17818c3702b86c0530b809e16812c2c01f85603b1200262380484600880401010c01e2100384100680400c00c0160000283c0048040080d400e1a0018330028040040a800614800828000804000, 0xf67801ecb003d8e2f031400f618ba0c1003d7e007aec00f5b803ab3003d5e2a02b401b558a60a9003d3e2e027400f4d8b6099003d2e007a4c02347803a8b003d0e290214019418a2081003cee2d01d800f398b20720074de2b81b801d358ac06a003cce27819850032801e631340c42701840212b803e53005c9e26013401525896049004c7e2500f40111d892039003c2e30005800f0a806014005c262f804800f0880601000041e00803800f0680600c003c162c002800f04806008003c0e2a801801d02806004003c061e000800100806000, 0x11678022cb00458e014b0c0115f8dc0bd0045763682e40115b8022b319c162008abc00355805e9f00b536008a5c6c04a8022931ac122008a3c011458cc08900450e015a0c0293b8d40750044e63481c40293780526b1940d201499c027318022570300ac0201540002a0022530100a400193c0102700804d00009800892c04025004a3f18807c3180f46101e00223b00442e3880580110a8080140094263800480110880801000441e3780380290680800c00441634002801104808008000c0e3200180110280800400440624800800300808000, 0x26cf004d96009b1c031618026bf004d76009adc03b598026af1f815a009aac7c0550fa0a91ec15001ca7c03f4d802697004d2601ca3c037458026871e810a009a0c780410f20811dc10001e9dc03139806a6f00ccd600999c760328062631d00c43a8184730300026570094a6310148630288c2050004c9e0281340132580a04a0300920001200131f80a03d000c760280e80101c800038004c2e4100580130a80a014004c264080480130880a010004c1e4000380310680a00c00f4163f80280130480a008004c0e2500180030280a004004c063900080130080a000, 0x1567802acb00558e4803140156191e0c100557e00aaec8b05c802ab701156600aabc00555802a9f23813a00aa6c8d04c802a9700552645024404947808e8b00550e021a0c0153b82a0760180ea0001d00153980c0720114de4401b8015358d206a0014ce008198060328000640054c60301880452b808a5321c0a402093c8402710a04d20c09800a92c0331f804e3b00542e4900580150a80c0140104264880480150880c01000541e4600380150680c00c0014164480280150480c00800540e4300180450280c0040054062580080050080c000, 0x2ecf005d9600bb1c01761802ebf007d7600badc04f59802eaf27815a00baac9c05513a0a926c15000ba7c0174d809a97014526026a3c04b45802e8726810a00ba0c9804113208125c1000109dc01f39802e6f0104d64201a885034906068005cce0381940173180e0620540c20001800352b805253005c9e3b013401f2592a04a2580924a01200171f80e03d0014760380e80101c800038005c2e5100580170a80e014005c265080480170880e01000841e5000380170680e00c005c164f802801f0480e008005c0e2600180050280e004005c064980080170080e000, 0x19679600cd006596578324019638032c32b418200cafc0195d8032b7014d6600cabc0015580329f07013c0402740004e00329b02013400ca5cab04b003293234124029a3ca804700328b1ac114000a1c0104301008500010800ca0c080410032770064e65501c80533780a66b29c0d400c99ca403314a06528c0c800c98c0572b80aa53012c9e02192c0371f80563b00642e5880580190a8100140064265700480190881001000041e5600380190681000c0064165480280190481000800640e5300180530281000400640628800800100810000, 0x1ecf003d96007b1c00f61801ebf007576007adc01b59801eaf2f015a007aacba0551760a92e4150007a7c00f4d804697007526007a3c0194594808a29411251822000f43812085003d060482081c0408000800164ee0289cc04d37802a6b003cce4d019400f3196e0622e00c25b01800392b802253003c9e3d013401d2596804a2d409259812000f1f81203d0004760480e80101c800038003c2e60005800f0a812014008c265f804800f08812010003c1e5f003800f0681200c003c165e802801d04812008003c0e29001800102812004003c0659000800f00812000, 0x1b678420ce02819a00033001b658140ca006d8e66031801b6195e0c2006d7e6482f801b5d91e0ba016d6e6302d801b598da0b200055e0082b80a0568000ac006d560502a801b4f80369b32c13400da5c01b49990092016d1e02da2cc504500368730810c618214c1042003683006cee00d9cc01b3780b66b006cce00098c05f2b80ba53013c9e00292c03b1f80063b006c2e67005801b0a81401400042666804801b08814010006c1e65003801b0681400c006c1663802801b04814008006c0e62001805b02814004006c0629800800100814000, 0x1ecf003d96007b1c00f61801ebf007576007adc01b599840b230c1626082c000f578160ad003d560582a8210548000a8003d3e007a6c0234b803a93003d1e00ca2c00f43978085003d066b8208d80409ac0800084ee00f9cc01737802a6b003cce4f019400f319a80623540c26981800132b802253003c9e3f013401d259a204a34809268012000f1f81603d0004760580e80101c800038003c2e6e005800f0a816014005c266d804800f08816010003c1e6d003800f0681600c003c166c802801d04816008003c0e2a001800102816004003c0667800800f00816000, 0x759e00eb2c01d63803ec300756e0a02d401d598260b100755e02daac0614f80a29b00751e09023401d4582208900750e029a0c03d3782006d007cd60781a401f33808a6300748e0601180c0228000440074860601080c020800040004c7e0280f80111d80803a00742e6f805801d0a818014004c266f004801d0881801000741e6e803801f0681800c00740e07001801d0281800400740614000800300818000, 0x3d013e79826cef04b9dc0933a811e74822cd90439880833b40ee7601cce80379ce06b2f40ce53018ce602b9ca05338409e70012c9f01f90c03b3dc0267b0048f500881a0103c801e788038f000681a00c038016000028eb00481a00839000e718018e200281a0041540061480082400081a000, 0xf67801ecb003d8e84031400f61a0e0c1003d7e007aec00f5ba020b50075668002c400f578036ab003d3e83027400f4da0a099003d2e007a4c023479fe08d0075167f022400f43803283003cee8201d800f39a06072003cde2781b8fd036801e6b1340d47e01a4001339f206600f4c67c01880212b9f6055007ca67d014401727802a4b00f47e3f80f80031d8c803a003c2e85005800f0a81c014005c2684804800f0881c01000741e06003800f0681c00c003c1681002800f0481c008003c0e75801801d0281c004003c061500080010081c000, 0x3ecf45819600fb1d14062803ec344c18200fafc01f5d803eb7007d6600fabc05d5580a29f44813a028a6d1104c80ca97014526031a3c0514580a28701550600f9dc1503b01e0750000e800f9cc0f039003e6f0300dc0781b400036003e6b03c0d401a99d0b0330052631a40c400f95d0d02b21c0554300a800f94c01f27808a4b21c0940188fc0291d8ca03a007c2e8b805801f0a81e014007c268a80480510881e010007c1e88003801f0681e00c00c41687802801f0481e008007c0e7d001801f0281e004007c061580080070081e000, 0x10b3c021658042c700858601eafc03d5d8042b7017d66010abd1d0568042ab470152010a7c0214d807a9700f52602ca3c0574580428746c10a010a0d1a040804277007ce68681c90e038a180700084de0229ac021338200650084c60801881503080006000f4ae01494c0212782004d00f4960801280c02480004800847e3b00f40091da3203901642e9000580210a8200140084268f80480210882001000841e8f00380210682000c0084167d802803d0482000800840e160018009028200040084068c000802100820000, 0x3acf4ac19a00eb2d2a064803ac700758600eafd2705d803ab700756600eabc05b55803a9f07013c0882740004e003a9b044134028a5d2604b00a29344412400ea3c0c04702208d00011800ea2c1104500728748410c008a0c6b04100c2770144e600e9bd2303724806d4880d800e9ac01d3380a66329c0c401e95c0512980a24f011c960098fc0111d8cc03a00742e96005801d0a82201400742694804801d08822010004c1e94003801d0682200c0074169280280510482200800740e7f001801d0282200400740617800800700822000, 0x11b3c023658046c7008d8600eafc01d5d8046b74c416a011acd300588046af006d56011a7c0234d80469700752691824924048a44090008d1e0902340234582408a0701120002200234380a68300f4ee0319cc02337a3606d008cd69781a404d33809263008cae09015401d298240520300a20001400132780224b008c7e3d00f800b1da5a03a01342e9a00580230a824014008c2699804802308824010008c1e9900380230682400c008c167f802801d04824008008c0e97001802302824004008c0618000800b00824000, 0x3acf08419c09833400066003acb04c19400eb1d3d063003ac34a818400fafd3b05f003ebb44c17400eadc0c05b0260b500016800eacc130590026af4d415c008aac6d055003a9f00753600ea5c01f49803a8f4dc11c9c023536046003a8b00750e02da0cc504100c2774e80e600e9bc01d35803a67014cc601e95c01f29803e4f0114960098fc0111d8ce03a00742e9f805801d0a8260140074269f004801d08826010004c1e9e003801d0682600c0074169c802801f0482600800740e80001801d0282600400740618800800300826000, 0x7b3c00f65801ec7003d86007afc01d5da6e0ba4e01729b02e000f5b8280b5003d660a02c8210588000b0003d5e02daac00f4f801e9b00752e00ea4c00f47a6208d003d16a1822400f4380328300f4ee00f9cc00f37a3a06d003cd6a101a401733802a63003cae0a015401d298280520300a20001400132780224b003c7e3f00f80011da8003a003c2ea3005800f0a828014005c26a2804800f08828010003c1ea2003800f0682800c003c1680802801d04828008003c0ea0801800f02828004003c0619000800100828000, 0x3d9e007b2c00f5f8360bd003d760d02e400f5b803eb3003d5e00daac00f4b832095003d260c02440234780a28b003d0e00ca0c00f2f82a05e0540ba00017000f2d82a05a0540b20001600212b820056007ca60781480172780e04e0054960301280311f80523b003c2ea4005800f0a82a014005c26a3804800f0882a010003c160b802800f0482a008003c0e71001801f0282a004003c061980080050082a000, 0x55813eaa826d5104baa009351011e9c822cda04398e08353c0eea701cd32037a4a06b2f80ce54818d4c02ba9605352809ea4812c8001f8de03b564026ac00495700882c01055001ea980395200682c00c05c0160000294d00482c00840800e718018dd00282c0041600061a00082500082c000, 0xf67801ecb003d8eb3831400f61acc0c1003d7eb182f400f5dac40b9003d6e00eacc00f578036ab003d3eb2827400f4dac8099003d2eb0825400f49ac0091008d1e00ea2c00f43803283003ceeaf81d84f03a801e735780e42681c402137a3c06e00c4d68781a8021339400660014c644818801d2baba0560084a6ae014800127ab604e008496ad01280131f80223b003c2eb4805800f0a82e014019c26b4004800f0882e010003c1ea6803800f0682e00c003c160a802800f0482e008003c0e72001801d0282e004003c061a80080010082e000, 0x1ecf5c819a007b2d71064801ec7003d86007afc00f5d801eb74e8166007abc01b55801e9f07013c0c02740004e001e9b060134007a5c1504b030095000128007a4c1804900a28f5ac11c028a2d11045009a875a810c00aa0c8d041001e775b40ecb701d56c03a001e73008cde0289ac00f338032632a80c401095c05129802e4f00549645012803f1f805a3b003c2eb9805800f0a830014003c26b8004800f08830010005c1eb7803800f0683000c003c16b2002800f04830008003c0e73801805102830004003c061c000800d00830000, 0x7b3c00f65801ec7003d86007afd7805e801ebb5dc172007adc06159801eaf006d56007a7c00f4dada09a5b8132b6026000f4b832095003d260c82481c048800090008d1e030a2c00f43803283003cee0c81d400f398320720540e20001c00213780ca6b005cce00a98c0232ba360560184a6ba814800f2793404e002c96ba01280391f805e3b003c2ebd005800f0a832014005c26bc804800f08832010003c1eb2803800f0683200c019c16bb002800f04832008003c0e74001806102832004003c061c800800b00832000, 0x1ecf08419c0d033400066001ecb068194007b1d81063001ec35c4184007afc1505f0340bd000178007aec1a05d003eb75f016c00facd13059002eaf5ec15c00aaac8f055001e9f003d36007a5d7e04b2fe0955f4128007a4c00f47803e8b003d0e00da0cc8041001e77003ce60119bd27035801e670064c601095c01f29802e4f0054964581280311f80523b003c2ec1805800f0a834014003c26c1004800f08834010005c1ec0003800f0683400c003c16b3002800f04834008003c0e74801801f02834004003c061d000800500834000, 0x7b3c00f65801ec7003d86bf03097f060afa0c0003d7e0d82f400f5d8360ba0841720002e000f5b803ab3003d5e00daac00f4f801e9b003d2ebc025400f49b0e091008d1e00ea2c00f43803283003cee0d81d400f398360720540e20001c002137803e6b005cce00a98c00f2ba3a0560074a6c2814800f2793c04e000496c201280131f80223b003c2ec4805800f0a836014005c26c4004800f08836010003c1eb3803800f0683600c003c16c3002800f04836008003c0e75001801d02836004003c061d800800100836000, 0x3d8e10031400f6183e0c1003d7e007aec00f5b803ab3003d5e00daac00f3f83807e0700fa0001f000f3d83807a0700f20001e000f3b832076003ce60c01c80233782406e0074d60881a800f338120660064c60401880212b80a253005c9e00a92c0131f80223b003c2ec5005800f0a838014005c1e0f003800f0683800c003c16a9002800f04838008003c0e78001801d02838004003c0620800800100838000, 0x62013ec0026d4504ba7809336c11e65022d93043b2408347c0ee8a81cca103792206b6440cec8018c8102b8e005363c09ec7012d8d01fb1803b658026ca80499400883a0105a001ea980394700683a00c424016788028de00483a00817c00e2100182600283a0040780060000098b00083a000, 0x1767b440cd005d96d0832401763802ec3005d7e009aec0175b8036b3005d5ed002b401755b3e0a9005d3ebc82780174dade09a008d2e99825801349a50092008d1e5f82380014595808a005d0ecf02184f042802e836741042682040213b803e73005cde0209ac01733b38065005cc6cd81840132b804a53004c9ecd013402325b3204900047ecc00f40231db2e039005c2ed180580170a83c014005c26c580480170883c010019c1eaa00380170683c00c005c167900280130483c008005c0e2180180010283c004005c060e00080170083c000, 0x1ecf08419c0f833400066001ecb07c194007b1c1c06303e0c5000188007b0c1f061001ebf69817c007aed7105d003ab769416c00eacd2a059001eaf69015c00caacaf055001e9f6a013cd48275a704e001e9b003d2e007a4c00f47803a8b003d0e00da0ccb041001e77003ce60119bc01d35801e670064c65681880212ba2c053005c9e00a92c0131f80223b005c2ed5805800f0a83e014003c26d5004800f0883e010005c1ed0803800f0683e00c003c16aa802800f0483e008003c0e79801801d0283e004003c062200080010083e000, 0x7b3c00f65b500ca6a4192d3832000f638400c5003d86100308210608000c0003d7e007aec00f5b803ab3003d5e00daac00f4f84009d003d361002681c04c800098003d2e007a4c02347803a8b003d0e00ca0c00f3baf0076003ce6d701c800f37a6206e0074d6d681a800f339780660004c6d601880212b803e53005c9e00a92c0131f80223b003c2ed8005800f0a840014005c26d1004800f08840010003c1ed7803800f0684000c003c16ab002800f04840008003c0e7a001801d02840004003c0622800800100840000, 0x3d4e108298210528000a4003d46108288210508000a0003d3e10027800f4d83e09a003d2e0d825800f49834092003d1e0a023801d4582608a003d0e05821801b41814082003cee0079cc02337803a6b003cce00c98c0212b803e53005c9e00a92c0131f80223b003c2611804800f08842010005c1eca003800f0684200c003c16ab802800f04842008003c0e7a801801d02842004003c0623000800100842000, 0x5e813eb9826d3404ba5809330011e58822db9043b700834800ee8b81cca203792406b6dc0cedb018c8202b8e20536d409eda012db301fb6403b68c026ca80498a0088440105a401eac00394800684400c4280167b0028df00484400818000e2380182700284400408c006000009b1000844000, 0xf67b600ce003d96d5032800f63b120c6003d86c1030800f5fa8c0be0075769f02e800f5b9b80b60005666682c800f57b860ae13c15a007aadc205509a0a9003d3e007a6c04d4b803a93003d1e00ca2c00f43b82085003d06e002040593b803e73005cde00a9ac00f33b7e065003cc6df01840132b80225300749ede813400f25b7804900047edd80f400f1db74039003c2ed8805800f0a846014005c26cb004800f08846010003c1eac803800f0684600c003c167b802801d04846008003c0e24001800102846004003c0610800800f00846000],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT7 : List ℕ := [0x340a0001b06821, 0x28060001c06c21, 0x34060001c06821, 0x28060442608821, 0x5c110001c06826, 0x50110001b06822, 0x34060502908821, 0x10000342106c1a, 0x1800028210681b, 0x1400028210701b, 0x18000342106c1a, 0x1000034210701a, 0x28000342106c1a, 0x44000502206c1a, 0x1400028210681b, 0x2400018210681c, 0x100005c260701a, 0x10000502206c1a, 0x1800028210701b, 0x440a0001d07026, 0x2800018210681c, 0x44060001d06c22, 0x4400018220681d, 0x1800044220681b, 0x24000182106c1c, 0x34000182106c1c, 0x2400044260741c, 0x3400028210701b, 0x1400044220741b, 0x5000044220741b, 0x140005c290701b, 0x40000182206c1d, 0x1800034210701a, 0x50060001d06822, 0x3400018210681c, 0x5000018220681d, 0x18000502206c1a, 0x2800034210701a, 0x1000050220741a, 0x4400050220741a, 0x4000018220681d, 0x3400028210681b, 0x5c00028260681d, 0x280005c260701a, 0x100005c260741a, 0x5000044220681b, 0x5c00044260681c, 0x440005c260701a, 0x1400044220681b, 0x24000502906c1c, 0x2400044260681c, 0x1000034270841a, 0x10040181b0681a, 0x18000001a0681a, 0x28000001a0681a, 0x44000001a0681a, 0x100005c290701b, 0x18000001b06c1b, 0x181b0681a, 0x18060181b0681a, 0x280a0181b06c1a, 0x44110181b06c1a, 0x181b06c1a, 0x281c0681a, 0x441d0681a, 0x2800044260741c, 0x10040281c0681a, 0x1800044220741b, 0x18060001c0701a, 0x18060001b06c1a, 0x18060341c0701a, 0x341c0681a, 0x3400050290741c, 0x18060341c06c1a, 0x1800050220741a, 0x280a0001b06c1a, 0x280a0001c0701a, 0x280a0341b06c1a, 0x341b0681a, 0x340005c290741b, 0x280005c260741a, 0x44110001b06c1a, 0x44110001c0701a, 0x44110501b06c1a, 0x500005c290701b, 0x44000502106c1a, 0x44000342106c1a, 0x34000502906c1c, 0x340005c290701b, 0x4000028260681d, 0x100005c260701b, 0x100005c290701a, 0x34060502608821, 0x10000502206c1c, 0x10000502906c1a, 0x340a05c2608821, 0x280a0281c0681a, 0x28000502206c1a, 0x10000342906c1a, 0x44110441d0681a, 0x2800044260681c, 0x1400044220681c, 0x10000502606c1a, 0x340a05c2908821, 0x10000342606c1a, 0x4400034210701a, 0x10000342206c1a, 0x1800028210701a, 0x28000182106c1a, 0x44000182206c1a, 0x440a0181b0681a, 0x18060281c0701a, 0x44110281c0701a, 0x28060001c06c1a, 0x44060001d06c1a, 0x440a0001d0701a, 0x340d0341c06c1b, 0x50140341c0701b, 0x34000001b06c1b, 0x50000001b06c1b, 0x2800044260741a, 0x3400050290741b, 0x4400028260701a, 0x5000034290701b, 0x1800044220741a]

def S7 (s i : ℕ) : List ℕ := unpackW wdT7 9 ((levT7.getD s []).getD i 0)

def N7 (s : ℕ) : ℕ := (levT7.getD s []).length

def A7 (s i tag : ℕ) : ℕ := findAct 4096 ((actT7.getD s []).getD i 0) tag

def W7 (w : ℕ) : ℕ := witT7.getD w 0

def Z7 (s : ℕ) := barrier 26 S7 N7 A7 W7 idRot s

theorem enc_inputs7 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT7) = xsT7 := by decide +kernel

theorem enc_goal7 : encL fT7 rowsT7 = goal 26 := by decide +kernel

theorem mask7 : mask 26 = 2 ^ rowsT7.length - 1 := by decide +kernel

theorem proper_fail7 : ∀ zs ∈ xsT7.sublists, zs ≠ xsT7 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked7 : ∀ s ≤ 8, ∀ i < N7 s, Z7 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun7 (s : ℕ) (hs : s ≤ 8) (h : NatRun (mask 26) (goal 26) s xsT7) : False := by
  have hc : NatRun (mask 26) (goal 26) 8 xsT7 := extend_run h hs
  have p : xsT7.Perm (S7 8 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked7 8 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub7 : ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsT7 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT7
  · subst e; exact noRun7 s hs h
  · exact proper_fail7 zs (List.mem_sublists.2 hz) e (required h)

theorem low7 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT7 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT7 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 8 h
  have hr : NatRun (mask 26) (encL fT7 rowsT7) s' (ws.map fun a => encL a rowsT7) :=
    Run.map (fun a : BFn 5 => encL a rowsT7)
      (fun a => by rw [mask7]; exact encL_inv a rowsT7)
      (fun a b => encL_and a b rowsT7) (fun a b => encL_or a b rowsT7) hrun
  rw [enc_goal7] at hr
  refine no_sub7 s' (by omega) _ ?_ hr
  rw [← enc_inputs7]
  exact hsub.map _

def mono7 : List Gate := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [10, 12]⟩]

theorem mono_ok7 : ∀ g ∈ mono7, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono7, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval7 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono7, 13⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve7 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeaa8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono7, 13, mono_ok7, ?_, mono_eval7⟩
  by_contra hlt
  have hlen : mono7.length = 9 := rfl
  apply low7
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 8
    omega

def rowsT8 : List ℕ := [1, 1, 1, 2, 2, 4, 5, 5, 5, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 9, 17, 3, 6, 6, 7, 13, 21, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT8 : List ℕ := [0x24c9f3c0001c7, 0x4b971e40e1c18, 0x9d3a7c070e1e0, 0xf23fa0b80fe00, 0xffe4413ff0000]

abbrev fT8 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT8 : List ℕ := [0x0, 0x100000000, 0x1e40001ff, 0x1000000000, 0x182c001e1f, 0x8200000000, 0x8a0800e3e7, 0x9a2c00ffff, 0x9b2c0001c7, 0x12000000000, 0x120c000fe38, 0x121e400ffff, 0x131e4001c18, 0x1a3c000e1e0, 0x1aac800ffff, 0x1ba0800fe00, 0x1bb2c00ffc7, 0x1bbec00ffff, 0x80000000000, 0x81124000000, 0x9bbec00ffff, 0xc00340f001f, 0x400400000000, 0x4087000001c0, 0x4404107101e7, 0x4897240001c0, 0x4c04347f01ff, 0x4c05340001c7, 0x900000000000, 0x9000c07f0038, 0x9001e47f01ff, 0x9121c0000000, 0x91bbec00ffff, 0x91bbec7fffff, 0x9801e40e0018, 0x9931e4000000, 0xd005c07001e0, 0xd1a7c00001c0, 0xd404d07f01ff, 0xdc04107f0000, 0xdc05347f01c7, 0xdc05f47f01ff, 0xdc15f47f01ff, 0xdd25f47f01ff, 0xdd25f47fffff, 0xddbe187ffe00, 0xddbffc7fffff, 0x2000000000000, 0x2009a08000000, 0x201bbec00ffff, 0x204081b810207, 0x2089b2c000000, 0x20c183c000007, 0x2409f080001c0, 0x2448e180001c7, 0x24c0410000000, 0x24c1534000000, 0x24c87100001c0, 0x24c9e18000000, 0x24c9e3c0001c7, 0x24c9f3c000000, 0x24c9f3c0001c7, 0x24d24d000fe38, 0x24dbf3c0001c7, 0x24dbffc00ffff, 0x2909ac87f0038, 0x29529db810207, 0x2dc05f47f01ff, 0x2dc9f3c0001c7, 0x2dc9ffc7f01ff, 0x2ddbffc0001c7, 0x4204000000000, 0x42040038f1e18, 0x420582f8f1e1f, 0x4217000001c00, 0x42850240e1c18, 0x4297124001c00, 0x42c40378f1e1f, 0x460c7038f1fd8, 0x4657410711de7, 0x4b160c00e1c18, 0x4b171c0001c00, 0x4b171e40e1c18, 0x4b840000e0000, 0x4b851240e0000, 0x4b8ca080ee3e7, 0x4b961c00e0000, 0x4b961e40e1c18, 0x4b970000e1c00, 0x4b971e4001c00, 0x4b971e40e0000, 0x4b971e40e1c18, 0x4b9f3e40e1c18, 0x4b9fbec0effff, 0x4f975e40e1c18, 0x4f9f7e40e1dd8, 0x4fd75f47f1dff, 0x620580b801e00, 0x621fa08001c00, 0x624481b8f1e1f, 0x628582f8e1e18, 0x62c40138f0000, 0x62c50378f1c18, 0x62c583f8f1e1f, 0x62c593f8f1e1f, 0x62cda3f8f1e1f, 0x62cda3f8fffff, 0x62de3d38fe1e0, 0x62dfbff8fffff, 0x66c5c3f8f1e1f, 0x66c5c3fff1fff, 0x66cdf3c0001c7, 0x66cdf3f8f1fdf, 0x66dff3c001dc7, 0x6b971e40e1c18, 0x6b9fbec0e1c18, 0x6bd79ff8f1e1f, 0x6f05dcbf01fe0, 0x6f5eed80e1ddf, 0x6fc44100e0000, 0x6fc5dffff1fff, 0x6fcdf3c0e01c7, 0x6fd75f40e1c18, 0x6fdfffc0e1c18, 0x6fdfffc0e1ddf, 0x9020000000000, 0x9020003f1e220, 0x9028a0bf1e3e7, 0x903a20000e000, 0x90a1127f1e220, 0x90fa2340fe01f, 0x942860070e1e0, 0x943a70000e1c0, 0x9460413f1e3e7, 0x99320c070e020, 0x99321c0000000, 0x99321c070e020, 0x993a2c070e020, 0x993a3c000e000, 0x993a3c070e1e0, 0x9d20400700000, 0x9d21c2c701e1f, 0x9d287007001c0, 0x9d324c070e020, 0x9d325c0700000, 0x9d325c070e1e0, 0x9d3a60070e000, 0x9d3a6c070e1e0, 0x9d3a7c000e1c0, 0x9d3a7c07001c0, 0x9d3a7c070e000, 0x9d3a7c070e1e0, 0x9d3afc870e3e7, 0x9d3b7c070e1e0, 0x9d3bfec70e1e7, 0x9d3bfec70ffff, 0x9d7a7d071e1e7, 0x9dba7c070e1e0, 0x9dbb7e470e1e0, 0x9dfa7f470e1e7, 0x9dfa7f47fe1ff, 0xb028a0b80e200, 0xb03ba0800e000, 0xb460413f10000, 0xb468e1bf1e3e7, 0xb469e1bf1e3e7, 0xb4735f7f11c18, 0xb47bffff1ffff, 0xb4e8e1bf1e3e7, 0xb4e9f3c0001c7, 0xb4e9f3ff1e3e7, 0xb4fbf3c00e1c7, 0xb9a8bef8ee218, 0xb9bbbec00e000, 0xb9f38fc70e027, 0xbd3a7c070e1e0, 0xbd3bfc870e1e0, 0xbd7afd870e1e7, 0xbd7afdbf1e3e7, 0xbdbbfec70e1e0, 0xbde0410700000, 0xbde8fffffe3ff, 0xbde9f3c7001c7, 0xbdf35f4700000, 0xbdfa7d070e1e0, 0xbdfb7f470e1e0, 0xbdfbfd870e1e0, 0xbdfbffc0001c7, 0xbdfbffc00e1c7, 0xbdfbffc7001c7, 0xbdfbffc70e1e7, 0xd224003fffe38, 0xd23600380fe00, 0xd23f20000fc00, 0xd23fa0b80fe00, 0xd6ad6247efdf8, 0xd6f653780ffc7, 0xdb24003ff0000, 0xdb2db2fff01c7, 0xdb360c3fffe38, 0xdb361c3fffe38, 0xdb3fbefffffff, 0xdbb71e40e1c18, 0xdbb71e7fffe38, 0xdbbf3e40efc18, 0xdf3e7c070e1e0, 0xdf3e7c3fffff8, 0xdf3f7c070fde0, 0xdfa44007e0000, 0xdfb75e47e1c18, 0xdfbe7c07ee1e0, 0xdfbf7e47efdf8, 0xdfe4413ff0000, 0xdff65f7ffffff, 0xf224003800000, 0xf2241e78001ff, 0xf22ca0b80e200, 0xf22da0b800000, 0xf22da0b80fe00, 0xf237003801c00, 0xf23e20380e000, 0xf23ea0b80fe00, 0xf23fa0800fc00, 0xf23fa0b801c00, 0xf23fa0b80e000, 0xf23fa0b80fe00, 0xf23facb80fe38, 0xf23fb0b80fe00, 0xf23fbef80fe18, 0xf23fbef80ffff, 0xf2bfa0b80fe00, 0xf2bfb2f80fe00, 0xf2ffa3f8ffe1f, 0xf63fe0b80fe00, 0xf63ff0b80ffc0, 0xf664413f10000, 0xf67fe1bf1ffe7, 0xf6e4413800000, 0xf6e4413ff0000, 0xf6ede1b800000, 0xf6ede3fffffff, 0xf6edf3f8001c7, 0xf6ffe1b80fe00, 0xf6fff3f80fe00, 0xf6fff3f80ffc7, 0xfb3fa0b80fe00, 0xfb3facbfffe38, 0xfb3fbcb80fe00, 0xfba40038e0000, 0xfbb71e78e1c18, 0xfbbfa0b8efe00, 0xfbbfbef80fe00, 0xfbbfbef8e1c18, 0xfbbfbef8efe18, 0xfbf78fffffe3f, 0xff24403f00000, 0xff3e7c3f0e1e0, 0xff3fe0bf0fe00, 0xff3ffcbf0ffe0, 0xff64413ff0000, 0xff7eedbffffff, 0xffbffeffefff8, 0xffe44107e0000, 0xffe44138e0000, 0xffe4413f00000, 0xffe4413ff0000, 0xffe44d3ff0038, 0xffe4513ff0000, 0xffe45f7ff0018, 0xffe45f7ff01ff, 0xffe5413ff0000, 0xffe5537ff0000, 0xffe5c3fff1e1f, 0xffec613ff0000, 0xffec713ff01c0, 0xffece1bffe3e7, 0xffede1bff0000, 0xffedf3fff0000, 0xffedf3fff01c7, 0xfff6413ff0000, 0xfff64d3fffe38, 0xfff65d3ff0000, 0xfff7413ff1c00, 0xfff75f78e1c18, 0xfff75f7ff0000, 0xfff75f7ff1c18, 0xfffe613ffe000, 0xfffe7d3ffe1e0, 0xffff7f7fffdf8, 0xffffe1bfffe00, 0xfffff3fffffc7, 0xfffffdbffffe0, 0xffffffc7efdff, 0xfffffff8effdf, 0xffffffff0ffe7, 0xfffffffff1ddf, 0xfffffffffe1e7, 0xffffffffffe18, 0xfffffffffffff]

def levT8 : List (List ℕ) :=
  [[],
  [],
  [],
  [0xee2fc74, 0xf02fc5c, 0xda2fc7b, 0x10a2b872, 0xe22e07a, 0xd72fc7c, 0xf22607c],
  [0x428e226077, 0x428e827c7d, 0x440e227c7d, 0x440e82607d, 0x428e226082, 0x428e82fc7d, 0x440e22fc7d, 0x428fc2fc7d, 0x474e22fc7d, 0x428e22b87d, 0x428e22e07d, 0x428f52fc74, 0x454f52fc5c, 0x3b8bf17031, 0x45ce22fc7b, 0x45cf32fc5c, 0x368bf17038, 0x428df0f824, 0x41ce20f824, 0x428fe2fc72, 0x428ae12c3e, 0x478e22fc7a, 0x388b81503e, 0x428a31683e, 0x388b516c3e, 0x428e22fc7c, 0x35cbf1703b, 0x488f22fc5c, 0x428e22bc5c, 0x428e21704f, 0x428c52605c, 0x428f52c474, 0x454f526074, 0x454f52c45c, 0x4289817042, 0x3b8981d03e, 0x3c0981703e, 0x3b89817034, 0x428f226074, 0x388c72605c, 0x45ce22e47b, 0x45cf32607b, 0x45cf32e45c, 0x388981703f, 0x368981ec3e, 0x3689817039, 0x3c8e22607b, 0x428e23103e, 0x428f835047, 0x468e235047, 0x468f83503e, 0x428e210c3e, 0x428e233447, 0x428e234847, 0x428ad2603e, 0x428981403e, 0x35c981703d, 0x388a72603e, 0x388981583e, 0x428761703e, 0x428831703e, 0x3886c1703e, 0x3888e1703e, 0x35c981f03e, 0x3c8981703b, 0x2605c0f82e, 0x360981703e, 0x428e22f05c],
  [0x10a388981703e, 0x10a388c82605c, 0x10a388bf1703e, 0x10a388a52603e, 0x10a388681703e, 0x10a2605c0f82a, 0xe22605c0f812, 0x10a388c829498, 0x10a388c81a05c, 0x10a388c821c5c, 0x10a320981702a, 0xe23209817012, 0x10a388c82fc5c, 0x10a388871703e, 0x10a388981f414, 0x10a388bf1f45c, 0x10a3889f1703e, 0x10a3a0981703e, 0x110388981703e, 0x10a388bf2943e, 0x10a3885c1243e, 0x10a2fc5c0f82a, 0xe22fc5c0f812, 0x10a388bf17018, 0x10a3d49817031, 0xee388981703e, 0x10a388981d03e, 0x10a388b11703e, 0x115388981703e, 0x1173889817038, 0x10a368981703e, 0x10a388981ec3e, 0x10a388b91703e, 0x10a3cc981703e, 0x10a388a51a03e, 0x10a294980f82a, 0xe2294980f812, 0x10a388d40f820, 0x10a3889817047, 0x10a3e0981703e, 0x11a388981703e, 0x10a3f89812c3e, 0x10a3888b1703e, 0x11e388981503e, 0x10a388911703e, 0x10a388711703e, 0x10a1a05c0f82a, 0xe21a05c0f812, 0x10a40c811703e, 0x1203888d1703e, 0x981703e0a812, 0x12235c981703e, 0x10a388c829468, 0x10a388c829487, 0x10a320a52602a, 0xe2320a526012, 0x10a388d432020, 0x10a388c92605c, 0x10a3e0c82605c, 0x11a388c82605c, 0x10a388cc26051, 0x10a388c82245c, 0x10a3f8c82604b, 0x10a388c822c5c, 0x11e388c826054, 0x10a388c82445c, 0x10a388c817049, 0x10a320681702a, 0xe23206817012, 0x10a388cf21c5c, 0x10a388c81c45c, 0x10a320871702a, 0xe23208717012, 0x10a40cc82045c, 0x120388c82345c, 0x10a388c82285c, 0x10a3dcc12605c, 0x10a388c82405c, 0x119388c62605c, 0xc82605c0a812, 0x12235cc82605c, 0x10a388c827c5c, 0x10a3a0c82605c, 0x110388c82605c, 0x10a388c82fca5, 0x10a388cc2fc5c, 0x10a388bf21c5c, 0x10a320bf1702a, 0xe2320bf17012, 0xee388c82605c, 0x10a388c826074, 0x10a388c82c45c, 0x115388c82605c, 0x10a368c82605c, 0x10a388c82607b, 0x10a388c82e45c, 0x10a3ccc82605c, 0x10a388a521c3e, 0x10a388891703e, 0x10a21c5c0f82a, 0xe221c5c0f812, 0x10a3888a1703e, 0x10a388901703e, 0x10a414e22607d, 0x10a3889f1f414, 0x10a3a0981f414, 0x110388981f414, 0x10a388981fc14, 0x10a3887d1a014, 0x10a2607d0a814, 0xe22607d05012, 0x10a3a0981f43e, 0x110388981f43e, 0x10a388bf1f414, 0x10a3889f1f45c, 0x10a388bf2947d, 0x10a388bf1f424, 0x10a3f8e22fc7d, 0x11e428e22fc7d, 0x10a388bf1fc5c, 0x10a388bf17047, 0x10a3887d17049, 0x10a2fc7d1702a, 0x428e235cbf1f45c, 0xe22fc7d17012, 0x10a388981f424, 0x10a388bf17026, 0x10a388981f434, 0x10a3f89818c3e, 0x10a388981f439, 0x11e388981e03e, 0x10a37c981703e, 0x107388981703e, 0x10a388951703e, 0x108388981703e, 0x10a388961703e, 0x10a380981703e, 0x428f2388981f45c, 0x10a388941703e, 0x10a378981703e, 0x104388981703e, 0x10a388a527c3e, 0x10a388641703e, 0x10a27c5c0f82a, 0xe227c5c0f812, 0x10a3a09f1703e, 0x1103889f1703e, 0x10a390981703e, 0x10c388981703e, 0x10a3a0bf1703e, 0x10a3a0a52603e, 0x10a3a0681703e, 0x10a2605c0f827, 0xe82605c0f812, 0x1103a0981703e, 0x10a3889a1703e, 0x10f388981703e, 0x110388bf1703e, 0x110388a52603e, 0x110388681703e, 0x1102605c0f82a, 0xe22605c0f80f, 0x10a3889e1703e, 0x10a39c981703e, 0x10a388691703e, 0x10a2605c0f82b, 0xe22605c0f815, 0x10a3d4bf17031, 0xee388bf1703e, 0x10a388bf1d03e, 0x115388bf1703e, 0x117388bf17038, 0x10a368bf1703e, 0x10a388bf1ec3e, 0x10a3ccbf1703e, 0x10a388bf29437, 0x10a388a51243e, 0x10a2fca50f82a, 0xe22fca50f812, 0x10a388bf17037, 0x125428e20f824, 0x10a37cbf1703e, 0x107388bf1703e, 0x10a3f0bf1703e, 0x11d388bf1703e, 0x10a3f8bf12c3e, 0x10a388ae1703e, 0x10a388bf1c85c, 0x11e388bf1503e, 0x10a388b81703e, 0x10a388bf1e85c, 0x10a3887117049, 0x10a170490f82a, 0xe2170490f812, 0x10a388bf1c45c, 0x10a388bf1683e, 0x127428a31703e, 0x109388bf1703e, 0x428d72fca31703e, 0x10a388bf16c3e, 0x129388b51703e, 0x10a384bf1703e, 0x388d72fcb51703e, 0xbf1703e0a812, 0x10a388bf1703b, 0x12235cbf1703e, 0x10a3c8e22fc5c, 0x10a3fce22fc5c, 0x10a388bf1805c, 0x10a388bf29418, 0x10a3885c12418, 0x10a2fc5c0a818, 0xe22fc5c06012, 0x10a388bf1701a, 0x10a388d40f824, 0x10a3e0bf1703e, 0x11a388bf1703e, 0x10a3f0981703e, 0x11d388981703e, 0x10a388bf17036, 0x10a40ca31703e, 0x10a388bf1703a, 0x120388b51703e, 0x10a388981683e, 0x109388981703e, 0x10a3889816c3e, 0x10a384981703e, 0x428f2388bf2605c, 0x10a388981743e, 0x112388981703e, 0x10a3889817c3e, 0x10a3a8981703e, 0x10a3d4d62605c, 0x10a3d4981d031, 0x10a3d4b117031, 0x1153d49817031, 0x10a3d4a526031, 0x10a3d46817031, 0x10a2605c0c41e, 0xf53b89817031, 0xf52605c0c412, 0x10a3d4981d03e, 0x1153d4981703e, 0xee2605c0f831, 0xee388a52603e, 0x10a3d49817034, 0x10a3f8981343e, 0xfe3b8981703e, 0xee388681703e, 0xee2605c0f82a, 0x10a3d4981703b, 0x1223b8981703e, 0x10b388981703e, 0x470ee388981703e, 0xf33b8981703e, 0xe22605c0f822, 0xe22605c0f811, 0x10a388981603e, 0x10a388921703e, 0xe2354981703e, 0x10a388982183e, 0x10a388741a03e, 0x10a260740f82a, 0x10a35c981d03e, 0xe2260740f812, 0x10a388b11d03e, 0x115388981d03e, 0x10a388b12943e, 0x10a3885c1383e, 0x10a2c45c0f82a, 0xe22c45c0f812, 0x115388b11703e, 0x115388a52603e, 0x115388681703e, 0x1152605c0f82a, 0x115368981703e, 0xe22605c0f80c, 0x11535c981703e, 0x10a388981cc3e, 0x10a388b01703e, 0x10a388a62603e, 0x10a3886a1703e, 0x10a3c89817031, 0xe22605c0f832, 0x117388ca2605c, 0x117388981ec38, 0x117388b917038, 0x1173cc9817038, 0x117388a526038, 0x1173886817038, 0x1172605c0e02a, 0x1173689817038, 0xe22605c0e00b, 0x117388981ec3e, 0x1173cc981703e, 0xda2605c0f838, 0x10a368a52603e, 0x1173889817039, 0x11e388981543e, 0x11e368981703e, 0x10a368681703e, 0x10a2605c0f829, 0x117388981703b, 0x122368981703e, 0x428fd368981703e, 0x10a2605c0f82d, 0xda2605c0f812, 0x10a38c981703e, 0x10a3889814c3e, 0x10a3888c1703e, 0x10a30c981703e, 0x10a388982003e, 0x10a3887b1a03e, 0x10a2607b0f82a, 0xe235c981ec3e, 0xe22607b0f812, 0x10a388b91ec3e, 0x10a3cc981ec3e, 0x10a388b92943e, 0x10a3885c1283e, 0x10a2e45c0f82a, 0xe22e45c0f812, 0x10a3ccb91703e, 0x10a3cca52603e, 0x10a3cc681703e, 0x10a2605c0f81f, 0xf32605c0f812, 0xf335c981703e, 0x10a388a92603e, 0x10a3886e1703e, 0x10a2605c1103e, 0xf23889817038, 0x10a388ab26037, 0x10a388b22943e, 0x10a388a51c43e, 0x10a294680f82a, 0xe2294680f812, 0x10a388b32103e, 0x10a40ca52043e, 0x120388a52343e, 0x10a3b4a22603e, 0xec388a52603e, 0x114388a42603e, 0x10a364a52603e, 0xa52603e0a812, 0x12235ca52603e, 0x10a388b21703e, 0x10a388a526047, 0x10a3e0a52603e, 0x11a388a52603e, 0x10a388a522c3e, 0x10a388a52443e, 0xec388981703e, 0x10a364981703e, 0x10a3c4e23503e, 0x10a388d411c20, 0x10a3e0d40f820, 0x11a388d40f820, 0x10a3883e0cc20, 0x10a3503e0a820, 0xe23503e08012, 0x10a388d417047, 0x10a388981703c, 0x10a36c981703e, 0xef388981703e, 0x10a388c02605c, 0x10a3886817047, 0x10a3888117047, 0x10a3888d17047, 0x10a2605c11c2a, 0xe22605c11c12, 0x10a3e09817047, 0x11a3889817047, 0x10a3e0681703e, 0x10a3e08b1703e, 0x10a2605c0f81b, 0xf82605c0f812, 0x11a3e0981703e, 0x10a3e0811703e, 0x10a3889817040, 0x118388981703e, 0x11a388681703e, 0x11a388911703e, 0x11a2605c0f82a, 0xe22605c0f808, 0x11a3888d1703e, 0x10a3889817045, 0x10a3d8981703e, 0x10a388cd0f820, 0x10a388d20f820, 0x10a2605c0f82c, 0xe22605c0f821, 0x10a388b41703e, 0x116388981703e, 0x10a3f8981c83e, 0x10a3f8b62603e, 0x10a3f86812c3e, 0x10a3f88b12c3e, 0x10a2604b0f819, 0xfe2604b0f812, 0x478fe35c981703e, 0x10a388651703e, 0x10a3f8981483e, 0x10a40c8b1703e, 0x10a388bd1703e, 0x10a3886f1703e, 0x10a22c5c0f82a, 0xe222c5c0f812, 0x12a35c981703e, 0x10a3889d1703e, 0x10a388981703d, 0x10a388971703e, 0x10a388981c05c, 0x10a388ce1703e, 0x10a388ba1703e, 0x10a3d0981703e, 0x11e388981e83e, 0x11e388a82603e, 0x11e388681503e, 0x11e388911503e, 0x11e260540f82a, 0xe2260540f807, 0x10a388671703e, 0x11e3889815c3e, 0x120388911703e, 0x10a388be1703e, 0x10a3886b1703e, 0x10a2445c0f82a, 0xe22445c0f812, 0x10a388991703e, 0x10a1c45c0f82a, 0xe21c45c0f812, 0x10a3887117035, 0x10a388751303e, 0x10a3a4621703e, 0x111388661703e, 0x681703e0a812, 0x12235c681703e, 0x10a40c791703e, 0x10a2045c0f816, 0x1032045c0f812, 0x10a388aa2605c, 0x10a388cb2603e, 0x1203886d1703e, 0x1202345c0f82a, 0xe22345c0f805, 0x10a2605c1181c, 0x10a2805c0f82a, 0x10a260610f823, 0x10d2605c0f82a, 0x10a2845c0f825, 0x10e2605c0f828, 0x10a388a01703e, 0x10d388981703e, 0x10a388981f03e, 0x10a388bb1703e, 0xd72605c0f83b, 0x1223c8981703e, 0x488fa35c981703e, 0x1222605c0f82f, 0xd72605c0f803, 0x10a388881703e, 0xe22605c10409, 0xe226c5c0f812, 0xe22605e0f80d, 0xe52605c0f812, 0xe22705c0f80e, 0xe62605c0f810, 0x10a3889b1703e, 0x10a394981703e],
  [0x10a388981703e, 0x428e22605c0f83e, 0x10a388c82605c, 0x428e2320981703e, 0x428e22607d1703e, 0x428e22605c0f814, 0x10a388bf1703e, 0x428e22fc981703e, 0x428e22605c0f818, 0x428f5388981703e, 0x428e22605c0f831, 0x45d0a388981703e, 0x428e22605c0f838, 0x428e22605c1703e, 0x10a388a52603e, 0x428e2294981703e, 0x428e2350981703e, 0x428e22605c0f820, 0x428fe388981703e, 0x428e22605c12c3e, 0x4790a388981703e, 0x428e22605c1503e, 0x428e2260981703e, 0x10a388681703e, 0x428e2260681703e, 0x42903388981703e, 0x428e2260811703e, 0x4810a388981703e, 0x428e22608d1703e, 0x428e2388981703e, 0x10a2605c0f82a, 0x428e22605c0f82a, 0x4890a388981703e, 0x428e235c981703e, 0x4290a388981703e, 0xe22605c0f812, 0x428e22605c0f812, 0x428e22fc5c0f83e, 0x428e2294980f83e, 0x428e21a05c0f83e, 0x428981703e0f82a, 0x388981703e0f812, 0x428e2320981705c, 0x10a388c829498, 0x428e2320a52605c, 0x428e2350c82605c, 0x428e23209817020, 0x428e2330c82605c, 0x428e23209817051, 0x428fe388c82605c, 0x428e2320981704b, 0x4790a388c82605c, 0x428e23209817054, 0x428e2320982605c, 0x10a388c81a05c, 0x428e2320981a05c, 0x428e233cc82605c, 0x10a388c821c5c, 0x428e23209821c5c, 0x42903388c82605c, 0x428e2320982045c, 0x4810a388c82605c, 0x428e2320982345c, 0x428e2320c82605c, 0x428f7388c82605c, 0x428e2320c12605c, 0x4650a388c82605c, 0x428e2320c62605c, 0x428e2388c82605c, 0x10a320981702a, 0x428e2320981702a, 0x4890a388c82605c, 0x428e235cc82605c, 0x4290a388c82605c, 0xe23209817012, 0x428e23209817012, 0x428e2320981f45c, 0x428e23209817014, 0x10a388c82fc5c, 0x428e2320bf1703e, 0x428e2320bf2605c, 0x428e23209817018, 0x4ad0a388981703e, 0x4ad0a388c82605c, 0x428e22605c0f801, 0x428e23209817001, 0x428f5388c82605c, 0x428e23209817031, 0x45d0a388c82605c, 0x428e23209817038, 0x428e2320a52603e, 0x428e2330981703e, 0x428e22605c1443e, 0x428e2320681703e, 0x428e233c981703e, 0x10a388871703e, 0x428e2260871703e, 0x428e2320871703e, 0x428f7388981703e, 0x428e2304981703e, 0x4650a388981703e, 0x428e2318981703e, 0x428c82605c0f82a, 0x388c82605c0f812, 0x10a388981f414, 0x428e22607d0f814, 0x428e22607d17014, 0x10a388bf1f45c, 0x428e22fc7d1703e, 0x428e22fc981f45c, 0x428e2294981f43e, 0x428fe388981f43e, 0x4790a388981f43e, 0x428e22607f1703e, 0x4950a388981703e, 0x428e22605c0f826, 0x4990a388981703e, 0x428e2260631703e, 0x4a10a388981703e, 0x428e2260781703e, 0x428e21f4681703e, 0x428981f45c0f82a, 0x10a388d72607d1703e, 0x388981f45c0f812, 0x42905388981703e, 0x10a3889f1703e, 0x428e227c5c0f814, 0x428e227c981703e, 0x428e22605c0f802, 0x10a3a0981703e, 0x428e82605c0f814, 0x428e8388981703e, 0x428e22605c0f804, 0x110388981703e, 0x440e22605c0f814, 0x4410a388981703e, 0x428e22605c0f813, 0x428e22fc5c0f814, 0x428e2294980f814, 0x428e21a05c0f814, 0x428981703e0a814, 0x388981703e05012, 0x428e22fcbf1703e, 0x428f5388bf1703e, 0x428e22fc5c0f831, 0x45d0a388bf1703e, 0x428e22fc5c0f838, 0x428e22fc5c1703e, 0x10a388bf2943e, 0x428e22fca51703e, 0x4950a388bf1703e, 0x428e22fc5c0f824, 0x428fe388bf1703e, 0x428e22fc5c12c3e, 0x4790a388bf1703e, 0x428e22fc5c1503e, 0x10a3885c1243e, 0x428e22fc5c1243e, 0x49d0a388bf1703e, 0x428e22fca31703e, 0x4a50a388bf1703e, 0x428e22fcb51703e, 0x428e2388bf1703e, 0x10a2fc5c0f82a, 0x428e22fc5c0f82a, 0x4890a388bf1703e, 0x428e235cbf1703e, 0x4290a388bf1703e, 0xe22fc5c0f812, 0x428e22fc5c0f812, 0x10a388bf17018, 0x428e22fc5c0f818, 0x428e22fc9817018, 0x428e22fca52603e, 0x428e2350bf1703e, 0x428e22fc5c0f820, 0x428e22605c0f824, 0x428e22fc681703e, 0x42903388bf1703e, 0x428e22fc811703e, 0x4810a388bf1703e, 0x428e22fc8d1703e, 0x428e22605c1243e, 0x49d0a388981703e, 0x428e228c981703e, 0x4a50a388981703e, 0x428e22d4981703e, 0x428bf2605c0f82a, 0x10a388d72fc981703e, 0x388bf2605c0f812, 0x428ff388981703e, 0x428e2260601703e, 0x428eb388981703e, 0x428e22605c0f806, 0x44d0a388981703e, 0x428e22605c0f817, 0x428e2294980f818, 0x428e21a05c0f818, 0x428981703e0a818, 0x388981703e06012, 0x10a3d49817031, 0x428f52605c0f831, 0x428f53889817031, 0x428f5388a52603e, 0x428fe3d4981703e, 0x428e22605c1343e, 0x428f5388681703e, 0x428e2260851703e, 0x428f52605c0f82a, 0x4890a3d4981703e, 0x428e22605c0f81e, 0x48d0a388981703e, 0xee388981703e, 0x3d4ee388981703e, 0x428ee388981703e, 0x3d4e22605c0f812, 0x428e2358981703e, 0x10a388981d03e, 0x428e2260740f831, 0x428e2260741703e, 0x10a388b11703e, 0x428e22c45c0f831, 0x428e22c4981703e, 0x115388981703e, 0x454e22605c0f831, 0x4550a388981703e, 0x428e22605c0f830, 0x428e2294980f831, 0x428e21a05c0f831, 0x428981703e0c42a, 0x428d72605c0f831, 0x388981703e0c412, 0x1173889817038, 0x45ce22605c0f838, 0x45d0a3889817038, 0x45d0a388a52603e, 0x47917388981703e, 0x428e22605c1543e, 0x45d0a388681703e, 0x428e22608f1703e, 0x45d0a2605c0f82a, 0x48917388981703e, 0x10a368981703e, 0x428e2368981703e, 0x45d0a368981703e, 0x45ce22605c0f812, 0x428e22605c0f80b, 0x428e2328981703e, 0x10a388981ec3e, 0x428e22607b0f838, 0x428e22607b1703e, 0x10a388b91703e, 0x428e22e45c0f838, 0x428e22e4981703e, 0x10a3cc981703e, 0x428f32605c0f838, 0x428f3388981703e, 0x428e2294980f838, 0x428e21a05c0f838, 0x428981703e0e02a, 0x388d72605c0f838, 0x388981703e0e012, 0x428e21a05c1703e, 0x428981705c0f82a, 0x10a388d72605c1703e, 0x388981705c0f812, 0x428e22aca52603e, 0x428e2294980f837, 0x428e2294982603e, 0x10a388a51a03e, 0x428e2294981a03e, 0x428e22cca52603e, 0x428e2294982103e, 0x42903388a52603e, 0x428e2294982043e, 0x4810a388a52603e, 0x428e2294982343e, 0x428e2294a52603e, 0x428ed388a52603e, 0x428e2294a22603e, 0x4510a388a52603e, 0x428e2294a42603e, 0x428e2388a52603e, 0x10a294980f82a, 0x428e2294980f82a, 0x4890a388a52603e, 0x428e235ca52603e, 0x4290a388a52603e, 0xe2294980f812, 0x428e2294980f812, 0x428e22ac981703e, 0x428e22605c0f837, 0x428e2350a52603e, 0x428e2294980f820, 0x4ad0a388a52603e, 0x428e2294980f801, 0x428fe388a52603e, 0x428e22949812c3e, 0x4790a388a52603e, 0x428e2294981503e, 0x428e2294681703e, 0x428e22cc981703e, 0x428e2260841703e, 0x428ed388981703e, 0x428e2288981703e, 0x4510a388981703e, 0x428e2290981703e, 0x428a52605c0f82a, 0x388a52605c0f812, 0x428e22605c0f81a, 0x10a388d40f820, 0x428e23505c0f820, 0x428e2350980f820, 0x428e2350681703e, 0x428e22605c0f833, 0x42906388981703e, 0x428e2308981703e, 0x4850a388981703e, 0x428e2344981703e, 0x428d42605c0f82a, 0x388d42605c0f812, 0x428f1388981703e, 0x10a3889817047, 0x428e22605c11c20, 0x428e22605c11c3e, 0x10a3e0981703e, 0x428f82605c0f820, 0x428f8388981703e, 0x428e22605c0f80a, 0x11a388981703e, 0x468e22605c0f820, 0x4690a388981703e, 0x428e22605c0f81d, 0x428e21a05c0f820, 0x428e22045c0f820, 0x428e22345c0f820, 0x428981703e0a820, 0x388981703e08012, 0x428e22605c0f834, 0x10a3f89812c3e, 0x428fe2605c12c3e, 0x428fe3889812c3e, 0x11e428fe388981703e, 0x428fe388681703e, 0x429033f8981703e, 0x10a3888b1703e, 0x428e22608b1703e, 0x428fe3888b1703e, 0x428fe2605c0f82a, 0x428fe35c981703e, 0x428e22605c0f819, 0x4a90a388981703e, 0x428f9388981703e, 0x3f8e22605c0f812, 0x428e2260721703e, 0x428e22d8981703e, 0x428e2340981703e, 0x46d0a388981703e, 0x428e22605c1203e, 0x428e21a05c12c3e, 0x428981704b0f82a, 0x388981704b0f812, 0x428e22605c0f839, 0x11e388981503e, 0x478e22605c1503e, 0x4790a388981503e, 0x4790a388681703e, 0x4811e388981703e, 0x10a388911703e, 0x428e2260911703e, 0x4790a388911703e, 0x4790a2605c0f82a, 0x478e235c981703e, 0x428e2370981703e, 0x478e22605c0f812, 0x428e22605c0f807, 0x428e22607a1703e, 0x428e22a0981703e, 0x428e234c981703e, 0x428fb388981703e, 0x428e21a05c1503e, 0x42898170540f82a, 0x38898170540f812, 0x428982605c0f82a, 0x388982605c0f812, 0x10a388711703e, 0x428e21c4681703e, 0x428e21a05c0f835, 0x428e21d4681703e, 0x428e21a05c1303e, 0x428e21a0681703e, 0x428e9388681703e, 0x428e21a0621703e, 0x4450a388681703e, 0x428e21a0661703e, 0x428e2388681703e, 0x10a1a05c0f82a, 0x428e21a05c0f82a, 0x4890a388681703e, 0x428e235c681703e, 0x4290a388681703e, 0xe21a05c0f812, 0x428e21a05c0f812, 0x428e2260711703e, 0x428e22605c0f835, 0x428e2260751703e, 0x428e22605c1303e, 0x4ad0a388681703e, 0x428e21a05c0f801, 0x428e9388981703e, 0x428e2260621703e, 0x4450a388981703e, 0x428e2260661703e, 0x42903388681703e, 0x428e2204681703e, 0x4810a388681703e, 0x428e2234681703e, 0x428981a05c0f82a, 0x388981a05c0f812, 0x428e22605c0f836, 0x428e22605c1483e, 0x10a40c811703e, 0x42903260811703e, 0x42903388811703e, 0x429032605c0f82a, 0x428e22605c0f816, 0x4910a388981703e, 0x42900388981703e, 0x40ce22605c0f812, 0x428e22b0981703e, 0x428e2334981703e, 0x428e2260791703e, 0x47d0a388981703e, 0x428e22607e1703e, 0x428982045c0f82a, 0x388982045c0f812, 0x428e22605c0f83a, 0x428e22605c15c3e, 0x1203888d1703e, 0x480e22608d1703e, 0x4810a3888d1703e, 0x4810a2605c0f82a, 0x428e2374981703e, 0x480e22605c0f812, 0x428e22605c0f805, 0x428e22dc981703e, 0x428e2348981703e, 0x428e22606d1703e, 0x42902388981703e, 0x428982345c0f82a, 0x388982345c0f812, 0x388e22605c0f812, 0x428981703e0a82a, 0x42898170460f82a, 0x428981703e0a81c, 0x428981845c0f82a, 0x428981703e0a823, 0x428a12605c0f82a, 0x428981703e0a825, 0x4390a2605c0f82a, 0x428981703e0a828, 0x4290a2605c0f82a, 0x981703e0a812, 0x428981703e0a812, 0x428e22605c1183e, 0x428e22605c0f81c, 0x428e2260611703e, 0x428e22605c0f823, 0x428e2284981703e, 0x428e22605c0f825, 0x4ad0a2605c0f82a, 0x428981703e0a801, 0x4390a388981703e, 0x428e22605c0f828, 0x4890a2605c0f82a, 0x428d72605c0f82a, 0x388981703e0a812, 0x428e22605c0f83b, 0x428e22605c1643e, 0x428e2260931703e, 0x12235c981703e, 0x488e235c981703e, 0x4890a35c981703e, 0x488e22605c0f812, 0x428e22605c0f803, 0x428f2388981703e, 0x428fa388981703e, 0x10a3e8e235c981703e, 0x42901388981703e, 0x428e22605c0f82f, 0x388d72605c0f812, 0x388981703e04812, 0x38898170410f812, 0x388981703e04809, 0x388981785c0f812, 0x388981703e0480d, 0x3889c2605c0f812, 0x388981703e0480e, 0x398e22605c0f812, 0x388981703e04810, 0x428e22605c1043e, 0x428e22605c0f809, 0x428e22605e1703e, 0x428e22605c0f80d, 0x428e2270981703e, 0x428e22605c0f80e, 0x428e6388981703e, 0x428e22605c0f810, 0x4ace22605c0f812, 0x388981703e04801],
  [0x10a388981703e, 0x428e22605c0f83e, 0x10a388c82605c, 0x428e2320981703e, 0x428e22607d1703e, 0x428e22605c0f814, 0x10a388bf1703e, 0x428e22fc981703e, 0x428e22605c0f818, 0x428f5388981703e, 0x428e22605c0f831, 0x45d0a388981703e, 0x428e22605c0f838, 0x428e22605c1703e, 0x10a388a52603e, 0x428e2294981703e, 0x428e2350981703e, 0x428e22605c0f820, 0x428fe388981703e, 0x428e22605c12c3e, 0x4790a388981703e, 0x428e22605c1503e, 0x428e2260981703e, 0x10a388681703e, 0x428e2260681703e, 0x42903388981703e, 0x428e2260811703e, 0x4810a388981703e, 0x428e22608d1703e, 0x428e2388981703e, 0x10a2605c0f82a, 0x428e22605c0f82a, 0x4890a388981703e, 0x428e235c981703e, 0x4290a388981703e, 0xe22605c0f812, 0x428e22605c0f812],
  [0x10a388981703e]]

def actT8 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x2a8200550200aa00, 0x1182002302004600, 0x1182002302004600, 0x568200ad02015a00, 0xc682018d02031a00, 0x548200a902015200, 0xfd8201fb0203f600],
  [0x0, 0x784180f08201e10203c200, 0x78c180f18201e30203c600, 0x5d4180ba8201750202ea00, 0x0, 0x25c1804b82009702012e00, 0x25c1804b82009702012e00, 0x3ca55067c180cf82019f02033e00, 0x1366d0684180d08201a102034200, 0xb19d41e52903ce4e058c180b18201630202c600, 0x4a9d809b3503d26602541804a82009502012a00, 0x239d80553a800074011c1802382004702008e00, 0x269d80233a80207401341802682004d02009a00, 0x154c40119840103000aa4d01549402a8e81551c80003801541802a8200550200aa00, 0x119d805b3a804074016c1802d82005b0200b600, 0x119d805b3a802074016c1802d82005b0200b600, 0x8cc40119840103000464d008c940118e81571c804038008c1801182002302004600, 0xf59881eb2503d63a07ac180f58201eb0203d600, 0xa98801525002a3a00541800a82001502002a00, 0x569581ed2a80605402b4180568200ad02015a00, 0x7c8e80ad1c80603802b4180568200ad02015a00, 0x579b81f13680806c07bc180f78201ef0203de00, 0x858e818d1c8080380634180c682018d02031a00, 0xf23902c4180588200b102016200, 0xf6390654180ca82019502032a00, 0x549d80a93a80a07402a4180548200a902015200, 0x2a4c40119840103001524d02a4940548e81f31c80a03802a4180548200a902015200, 0x14e76008cea0081d01f73703ea6205e4180bc8201790202f200, 0x0, 0x0, 0x0, 0xf27601e41803c8200790200f200, 0xf27601e41803c8200790200f200, 0xf27601e41803c8200790200f200, 0x0, 0x3566101c49402a9240002403523d01541802a8200550200aa00, 0x3892802324802048008c1801182002302004600, 0xd79881f92503523a06c4180d88201b102036200, 0x1ab3b036e62006c1800d82001b02003600, 0x0, 0xf67501ec1803d82007b0200f600, 0xf67501ec1803d82007b0200f600, 0xf67501ec1803d82007b0200f600, 0x0, 0x3766101c4940119240202403723d008c1801182002302004600, 0xde9881bd2503723a06e4180dc8201b902037200, 0x1bb3a83864a00441800882001102002200, 0x0, 0x1f41803e82007d0200fa00, 0x1f41803e82007d0200fa00, 0x1f41803e82007d0200fa00, 0x0, 0x8c1801182002302004600, 0x8c1801182002302004600, 0x0, 0x0, 0x9880012500023a00041800082000102000200, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xec9881db3080c06001c4940eb9240502400023d00041800082000102000200, 0x1fb3283f66207ec940fd8e81fd1c80c03807ec180fd8201fb0203f600, 0x0, 0x0, 0x8c1801182002302004600],
  [0x172500221000441800882001102002200, 0x220a, 0x5c9a00b9280131c802e10005c1800b82001702002e00, 0x220a, 0x220a, 0x2202, 0x2202, 0x0, 0x0, 0x220a, 0x0, 0x0, 0x2e0a, 0x172500221000441800882001102002200, 0x8f41011a62022c940398f40731d00e61001cc180398200730200e600, 0xa9a0415130802e5500ac9a0098f40131d002610004c1800982001302002600, 0xb9280751c802a1000541800a82001502002a00, 0xb9280731d002a1000541800a82001502002a00, 0xb9280731d003e10007c1800f82001f02003e00, 0x2e06, 0x2e06, 0x2e02, 0x2e02, 0x1dc9a03b9280b31c80ee1001dc1803b8200770200ee00, 0x3ca780794100f26501e4c403c9280791d00f21001e41803c8200790200f200, 0x22990554d402a9980712500221000441800882001102002200, 0x6d3a02398807125003610006c1800d82001b02003600, 0x172500221000441800882001102002200, 0x6d3a02698807125003610006c1800d82001b02003600, 0x3da7407b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x369a055d14011a1807125003610006c1800d82001b02003600, 0x453c02da080712500221000441800882001102002200, 0x172500221000441800882001102002200, 0x453c02da080712500221000441800882001102002200, 0x0, 0x0, 0x0, 0x7d4100fa6201f49a03e92807d1d00fa1001f41803e82007d0200fa00, 0x4695008cea00f94801725004610008c1801182002302004600, 0x89d40172500221000441800882001102002200, 0xda5401725003610006c1800d82001b02003600, 0x813a81026d0204d40569280f91d01021002041804082008102010200, 0x89c80712500221000441800882001102002200, 0x10d4a80228d00451405792810b1d00221000441800882001102002200, 0xda4807125003610006c1800d82001b02003600, 0x220a, 0x0, 0x0, 0x419d408339010610020c1804182008302010600, 0x43a5408749010e10021c1804382008702010e00, 0x0, 0x8a740114d000e8a00050c0009880712500221000441800882001102002200, 0x0, 0x0, 0x0, 0x0, 0xfa06, 0x220a, 0x220a, 0x360a, 0x0, 0x220a, 0x1020a, 0x220a, 0x220a, 0x360a, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1060a, 0x10e0a, 0x220a, 0x0, 0x220a, 0x0, 0x0, 0x220a, 0x2a0a, 0x2a0a, 0x3e0a, 0x0, 0x1520a, 0x4606, 0x0, 0x0, 0x220a, 0x360a, 0x220a, 0x360a, 0x360a, 0x220a, 0x220a, 0x220a, 0x220a, 0x172500221000441800882001102002200, 0x2202, 0x2202, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x3200e60e, 0x44a0808b408040800224c40459840103001164d022c940458f408b1d011610022c1804582008b02011600, 0x44a08159408060800234ca046988089250116490040900468f408d1d011a1002341804682008d02011a00, 0x47a1408f410112620564c2018180089250116490080900478f408f1d011e10023c1804782008f02011e00, 0x401c00e606, 0xe606, 0xe606, 0xe602, 0x1cd020469940972500e6490140900398f40731d00e61001cc180398200730200e600, 0x23d0a0399840972500e6490180900398f40731d00e61001cc180398200730200e600, 0xada080974080c080056cc404b98405030012e4d025c9404b8f40971d012e10025c1804b82009702012e00, 0x754080ea6105749a03a8f40751d00ea1001d41803a8200750200ea00, 0x2606, 0x954a8056820585020402001633a805662057cc20381800952900564d00ac940158f402b1d00561000ac1801582002b02005600, 0xa8a641514a82a2750544e40b39b80a33681206c00bccc0b29481652702a2100544180a88201510202a200, 0xa9a741534d02a29205ad1c03aa340a046002686054cec0b49a81693302a610054c180a98201530202a600, 0x2606, 0x11a540553a802652005c9a00b9280131c802e10005c1800b82001702002e00, 0x2602, 0x2602, 0x4fb200136002a6a8004d300a8a0002334002660, 0x2602, 0x12a95026d0404a9d409931012a5205749404a8f40951d012a1002541804a82009502012a00, 0x1dc9a03b9280b31c80ee1001dc1803b8200770200ee00, 0x39a7408f41011a62022c940398f40731d00e61001cc180398200730200e600, 0x813a81026d0204d40569280f91d01021002041804082008102010200, 0x39a7808f41011a62022c940398f40731d00e61001cc180398200730200e600, 0x10d4a80228d00451405792810b1d00221000441800882001102002200, 0xb69580172500221000441800882001102002200, 0xf9580172500221000441800882001102002200, 0x712500221000441800882001102002200, 0x712500221000441800882001102002200, 0x7125003610006c1800d82001b02003600, 0x7125003610006c1800d82001b02003600, 0xb9b000115a02e2a8004518039a1001b3602de60, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x2a0a, 0x2a0a, 0x2a02, 0x2a02, 0x2e4a022c7404c8e40101c002a1000541800a82001502002a00, 0x2e4a022c7404d8e40201c002a1000541800a82001502002a00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x1726802e4a025c740158e40501c002e10005c1800b82001702002e00, 0x2a0a, 0x2a0a, 0x2a02, 0x2a02, 0x2e4a024c740ba8e40301c002a1000541800a82001502002a00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x1726802e4a025c740098e40601c002e10005c1800b82001702002e00, 0x3e0a, 0x3e0a, 0x3e02, 0x3e02, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x220a, 0x2202, 0x2202, 0x474f00aa9d034138023a0804d40818080011cca02398804726808e4a011c740248e40b01c008e10011c1802382004702008e00, 0x38a640a74082ee76001cd40389980553281a06401c49a03892809f1c80e21001c4180388200710200e200, 0xe29d02a50a0389880473081606001c49a03892802f1c80e21001c4180388200710200e200, 0xe29d02a50a03898804d3081806001c49a03892802f1c80e21001c4180388200710200e200, 0x234f00b69d04013802da1405b4100b662016cc207818005b2680b64a016c740bc8e40e01c00b610016c1802d82005b0200b600, 0x38a6817b4b00168a01c50c011a1410042014e6101c49a0389280a11c80e21001c4180388200710200e200, 0xe29e01c50402da040e04001526501c49a0389280131c80e21001c4180388200710200e200, 0xe29e01c50402da040f04001526501c49a0389280131c80e21001c4180388200710200e200, 0x15206, 0x0, 0x0, 0x0, 0x2a49a0549280131c81521002a4180548200a902015200, 0x154f00569d048138019a5802b4a82209400ad1a015a2802b4280568200acc401592802b1d00561000ac1801582002b02005600, 0xb69580ab2a822054005c9a00b9280131c802e10005c1800b82001702002e00, 0xa9580ab2a824054005c9a00b9280131c802e10005c1800b82001702002e00, 0x1a4ea00b9b401726802e4a03cc740158e40701c002e10005c1800b82001702002e00, 0xe52a00ba3401726802e4a03d4740098e40801c002e10005c1800b82001702002e00, 0x569d817d3a82807402b4da0569a80ad26815a4a03e4740568e41301c015a1002b4180568200ad02015a00, 0xc2a740693903066e02b4da0a01b01813100e24a05fc740518e40901c00d21001a4180348200690200d200, 0x5cec0c39880ad30826060005caa00b9340131d002e10005c1800b82001702002e00, 0x57a581894a82c09402bd1a057a280af26815e4a042c740578e41501c015e1002bc180578200af02015e00, 0xc7a780394900728e06351a0b02300ed4100e24a062c7403a8e40a01c00721000e41801c82003902007200, 0x5d2c00ba080af4082a080005caa00b9340131d002e10005c1800b82001702002e00, 0x4602, 0x0, 0x0, 0xb9540231d004610008c1801182002302004600, 0x5cec0589d41703a002e6a005c9a00b9280171c802e10005c1800b82001702002e00, 0xb14e81629502c5240c8a380b14682e08c02c50a058a080791c81621002c4180588200b102016200, 0x173b002e6a005c9a00b9280171c802e10005c1800b82001702002e00, 0x1c57000ba6001748032680, 0x5d2c0caa541804a002e8a005c9a00b9280171c802e10005c1800b82001702002e00, 0x6f4e80de9501bd240cba3806f4683008c01bd0a037a0807b1c80de1001bc1803782006f0200de00, 0x174b002e8a005c9a00b9280171c802e10005c1800b82001702002e00, 0x1c57000ba600174802f280, 0x0, 0x54a780a94e83409c02a5040549880a92681524a02a47404f8e41901c01521002a4180548200a902015200, 0x714e80e29a06652c003a28071430152850681080389880a73083606001c49a03892809f1c80e21001c4180388200710200e200, 0x29d3c0bca4819b4883609005e51c0bca080a73a800a6e008cc40c995819b25014e10029c180538200a702014e00, 0x1c03600ee0e, 0xcea040b730817e5502fc9a0598f40b31d01661002cc180598200b302016600, 0xee06, 0x1d01c00ee06, 0xee06, 0xee02, 0x2fc9a05f9280b31c817e1002fc1805f8200bf02017e00, 0x2a950055040199d40153100565200549a00a9280151d002a1000541800a82001502002a00, 0x2275005c9a00b9280131c802e10005c1800b82001702002e00, 0x3695005c9a00b9280131c802e10005c1800b82001702002e00, 0x2a7500e4da00b92819f1d002a1000541800a82001502002a00, 0x3e95007d1a00b9281a11d003e10007c1800f82001f02003e00, 0x2ec9a05d9281a31c81761002ec1805d8200bb02017600, 0x18a750314e40629b80b131018a100314180628200c502018a00, 0x1dc9a03b9280b31c80ee1001dc1803b8200770200ee00, 0x2295004524098a3806f4100221000441800882001102002200, 0x31cea01c9a80172500321000641800c82001902003200, 0x3f9a80172500221000441800882001102002200, 0x6552a00fa280172500de1001bc1803782006f0200de00, 0xd2a280172500221000441800882001102002200, 0x1a7600022bc00452803ba300113a014e50, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x1e03a00f20a, 0x1e53c03ca080794084008001e4ca03c9880792500f24907c09003c8f40791d00f21001e41803c8200790200f200, 0x1e53c03ca080794084208001e4ca03c9880792680f24a01e4740678e41f01c00f21001e41803c8200790200f200, 0x1e53c03ca140794100f26501e4c403c9280792484204801e4740678e42001c00f21001e41803c8200790200f200, 0xf20a, 0xf20a, 0x2201c00f202, 0x794e80f29a01e524068a380794280f28201e4c403c9280791d00f21001e41803c8200790200f200, 0xf202, 0x23a780554e84609c0075020239940473100e24a011c920581200d31e808e10011c1802382004702008e00, 0x26a780234e84809c01e50a02699404d3100e24a0134920601200791c809a1001341802682004d02009a00, 0xd5a24055410046810901000389a80553481a0680154c40d49540552502aa4908c09002a8f40551d00aa1001541802a8200550200aa00, 0x220a, 0x1aa9e06c53a1282701af4101aa650354c40d69280d31d01aa1003541806a8200d50201aa00, 0xd73a81ae6d035cd40d99280f91d01ae10035c1806b8200d70201ae00, 0x74d02aa9505551a0aaa28001430362850941080039280071d02aa100554180aa8201550202aa00, 0x220a, 0x2202, 0x3ca780794100f26501e4c403c9280791d00f21001e41803c8200790200f200, 0x8a740114d000e8a00050c0009880712500221000441800882001102002200, 0x1b525010e10021c1804382008702010e00, 0x22cc001d80011af00115a00228c, 0x8a740114d000e8a00050c0009880712500221000441800882001102002200, 0x2202, 0x10e02, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x3606, 0x3606, 0x3602, 0x369d006d34005a2800143000262006cc213018007125003610006c1800d82001b02003600, 0x3602, 0x1b4e808e6201e4c20f818007125003610006c1800d82001b02003600, 0x1b4e808e6201e4c210018007125003610006c1800d82001b02003600, 0x2206, 0x2206, 0x2202, 0x2202, 0x1b4e808e6201e4c210818007125003610006c1800d82001b02003600, 0x360a, 0x360a, 0x3602, 0xda7401b4d00168a00050c00098807125003610006c1800d82001b02003600, 0x3602, 0x6ea740dd4d00168a00050c0009880712501ba1003741806e8200dd0201ba00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x220a, 0x220a, 0x1ab4f036e8a006d0400d99401b3100364a006c740d48e42601c003610006c1800d82001b02003600, 0x2202, 0x2704a00f60a, 0x1ed3a03da1407b4100f66201ecc214818007b2500f6490a009003d8f407b1d00f61001ec1803d82007b0200f600, 0x1ed3a03da1407b4100f66201ecc215018007b2680f64a01ec7406f8e42801c00f61001ec1803d82007b0200f600, 0x1ed3a03da1407b4100f66501ecc403d92807b2485404801ec7406f8e42901c00f61001ec1803d82007b0200f600, 0xf60a, 0xf60a, 0xf602, 0x7b4e80f69a01ed2406fa3807b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x2b01c00f602, 0x11a7805b4e85809c016d0a02da080193080e24a016c920701200e31e80b610016c1802d82005b0200b600, 0x11a7805b4e84809c016d0a02da0807b3280e24a016c9207812007b1c80b610016c1802d82005b0200b600, 0xdda24023410046810901000389a802334820068008cc40dc9540232502ae490b00900118f40231d004610008c1801182002302004600, 0x360a, 0x3729e038d3a1682700e34281c68206f4c40de9280e31d01c610038c180718200e30201c600, 0xe54a81ca8d0395140df92810b1d01ca100394180728200e50201ca00, 0xb4d02ae95055d1a0aba28001430372850b410800592800b1d02ae10055c180ab8201570202ae00, 0x360a, 0x10602, 0x3da7407b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x73a740e74d000e8a00050c0009880712501ce10039c180738200e70201ce00, 0x16c8006d38011a5001b4600366c, 0x3602, 0x3602, 0x1c125010610020c1804182008302010600, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x229d004534003a28001430002620044c21701800712500221000441800882001102002200, 0x2202, 0x114f00b68201ed021402000712500221000441800882001102002200, 0x114f00b68201ed021482000712500221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x2202, 0x114f00b68201ed021502000712500221000441800882001102002200, 0x220a, 0x220a, 0x2202, 0x2202, 0x8a740114d000e8a00050c0009880712500221000441800882001102002200, 0x220a, 0x220a, 0x2206, 0x1bb4e8022850045040e19a80113100224a0044740dc8e42e01c00221000441800882001102002200, 0x0, 0x2206, 0x0, 0x0, 0x0, 0x0, 0x1060a, 0x10e0a, 0x0, 0x220a, 0x0, 0x220a, 0x0, 0x220a, 0x172500221000441800882001102002200, 0x460a, 0x220a, 0x360a, 0x220a, 0x360a, 0x3f9a80172500221000441800882001102002200, 0xa1a280172500221000441800882001102002200, 0x2f03600fa0e, 0x3ea0807d4086208001f4c403e9843003000fa4d01f49403e8f407d1d00fa1001f41803e82007d0200fa00, 0x3ea0807d4086408001f4ca03e98807d2680fa4a01f47403e8e43001c00fa1001f41803e82007d0200fa00, 0x3ea1407d4100fa6201f4c219018007d2680fa4a01f47403e8e43101c00fa1001f41803e82007d0200fa00, 0x3301c00fa06, 0xfa06, 0xfa02, 0x3e95007d120129d402534803e55007ca40099280151f003e10007c1800f82001f02003e00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x460a, 0x460a, 0x8d2a0119d402339003e52008ca21a014000525004610008c1801182002302004600, 0x8d2a011a480233a803e52008ca21a814000525004610008c1801182002302004600, 0x4602, 0x4602, 0x11a540233a803e5201f4a218014001725004610008c1801182002302004600, 0x11a540233a803e5201f4a218814001725004610008c1801182002302004600, 0x220a, 0x44ea0089c80f32500221000441800882001102002200, 0x2202, 0x2202, 0x11a540233a838a5201f4a219014001725004610008c1801182002302004600, 0x214ea0429c812925010a1002141804282008502010a00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x360a, 0x6d2a00da480f525003610006c1800d82001b02003600, 0x3602, 0x3602, 0x3dd2a07ba4813b2501ee1003dc1807b8200f70201ee00, 0x172500221000441800882001102002200, 0x172500221000441800882001102002200, 0x8d040119880232680464a008c740028e43401c004610008c1801182002302004600, 0x8d040119880232680464a008c740028e43501c004610008c1801182002302004600, 0x2202, 0x2202, 0xb9280a31c81b21003641806c8200d90201b200, 0x14e8002850004c40389280731d00021000041800082000102000200, 0x1c94081f275071cda0e39940f925015a4904c09007c8f40f91d01f21003e41807c8200f90201f200, 0x3603a01020a, 0x1020a, 0x102990204ea0409c80813681026a03e4cc0569280f91d01021002041804082008102010200, 0x37024010202, 0x10202, 0x76402066c, 0x220a, 0x253a82026d0404d40b29281cb1d02021004041808082010102020200, 0x659d40cb39019610032c180658200cb02019600, 0x5b4080aa6501c49a0389280131c80e21001c4180388200710200e200, 0x220a, 0x2202, 0x2202, 0x1d3a003a680074a800e8d001d14000a1800742870084001cc40039280071d000e10001c1800382000702000e00, 0x1832500221000441800882001102002200, 0x53c000a743804e0002820004c40009280011d00021000041800082000102000200, 0x172500221000441800882001102002200, 0xe50403f9880172900221000441800882001102002200, 0xe51403f9a80172500221000441800882001102002200, 0xb9280751c80721000e41801c82003902007200, 0x14f0002820004ca0389280731d00021000041800082000102000200, 0x10b4a839a8d07350a00c98410b25015e490540900858f410b1d021610042c1808582010b02021600, 0x3904a00220a, 0x220a, 0x21a9a04352a086a4810d46821a8a042d0c0e792810b1d021a1004341808682010d02021a00, 0x2202, 0x3a024002202, 0x10a0a, 0x1f4a82268d044d140b49281d11d022610044c1808982011302022600, 0x66a540cd49019a100334180668200cd02019a00, 0x2342809a6101c49a0389280131c80e21001c4180388200710200e200, 0x360a, 0x3602, 0x3602, 0x3925010a1002141804282008502010a00, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x220a, 0x3b03a01060a, 0x3c030010602, 0x10602, 0x29440231f00221000441800882001102002200, 0x119540051d00221000441800882001102002200, 0x3d04a010e0a, 0x10e02, 0x3e030010e02, 0x0, 0x7202, 0x0, 0x28602, 0x0, 0x0, 0x172500721000e41801c82003902007200, 0xb9281d31d028610050c180a182014302028600, 0x14f00029d0fc138000a080013100e24a051c920c81200011e80021000041800082000102000200, 0x172500221000441800882001102002200, 0x3b28a076d12200220001410046810901000389a81d7348340680004c40009540012503aa490fc0900008f40011d00021000041800082000102000200, 0x14f00469d090138003a281d94303ba851001080009940013100e24a069c920d81201731c80021000041800082000102000200, 0xec8004538011a500114600226c, 0x41042002202, 0x42040002202, 0x11a480233900465101c49401192443024004610008c1801182002302004600, 0x0, 0x29602, 0x0, 0x29a02, 0x0, 0x0, 0x1725029610052c180a582014b02029600, 0xb9281df1d029a100534180a682014d02029a00],
  [0x229f004536008a5c0114980228f007d16008a1c01d418022770044e60089bc025358036670064c601195c0212980224f005c960101280151f80263b0044260300480110880001000a41e0280380110680000c009c160200280110480000800440e01801801f0280000400440600800800100800000, 0x1156803aa9006d0a00ca040113280e262005cc20101800152680264900046c0008d40001a0002320004620000c00010a00021000041800082001101000200, 0x240aa0580480100801400e00401800882c0000500200802000c00801007001002000, 0x22c5004582008a740114c8022760044ea0681d001139003e6e007cd400899801131002e4a0300900088500110800020e00441800882001102002200, 0x22bd006d72009ac401b4a80229100bd120119d401138800662004cc207818001f2b0026550000a80099480012700264d0000980099280731f00ea3d0380780098500130800260c00441400982001302002600, 0x8ab401555003ea9048150008a1401541004a8104410000b9a801132802a620054c20801800732900ea510380a000a93401525003e4900009000a8f40151d00023900007000a85001508002a0c00541000a81001101002a00, 0x38a7c0714d802e97005d2600ba3c0174580e28701c50601f9dc01739802e6f00fcd603899c07131802e57005ca603893c02026802e4b00809400b8fc0031d81e039005c260b004801708804010005c1e0a803803f0680400c005c160a002801704804008005c0e09801801702804004005c0606000807100804000, 0x8b1406f60802ebd005d72008a740194c807e95010d220089d80173a800074005ce400b9c402038002a6e0044d400099801732800064005cc400b95801729002e4e01dc9a0b813001725002639005c2800b84001107002e0c01c41400b82001702002e00, 0x455a008aa401142802281005cd403b9a4170340022650044c40089840003000224d007c920088f40111d0002390000700088500110800220c00441000881001101002200, 0x32ce00459a0c8330019648032c100453c00ca740004e00329a00452c00ca480394700228a00050c00ca14000420032820124d40239980793283006401c49400c8500290900321000641800c82001902003200, 0x6d9a008ab401b550036a9070150023a2807944830088006d0a00da080114080008001c4d400899401b3100226106c0c000893401b25004a4906809000d8f401b1d00023900007000d85001b0800360c006c1000d81001101003600, 0x22ce00759a00033001d650036c600758a0f0310019610022be01bd7400fad801b590002ae00755a0002b001d55003a9a01751402da1807b4283a08401c49400885801d0a003a1000741800e82001d02003a00, 0x459c02dac807b5883a0b000455a008aa8011548000a800450a008a080114084208001c4d4008994011310022610800c000893401125003e4907c0900088f40111d0002390000700088500110800220c00441000881001101002200, 0x22b5007d62008a340254480466d0084d200b98801f23003e4500008800f90801f2080004000547c0098e801f0a003e10007c1800881801f02003e00, 0x4c0741200480300804600e00c01800882c0000500600808800c01801007001006000, 0x11628022c100453a008a640113b0022720044dc0089a800133007262005c9400885001108003e0e00441800882001102002200, 0x22c5008582008a740214c8022760084ea0001d002139003e6e0084da0001b002135002a660044c400f95807d2a84a054005c9401085002108004e0e00841801082002102004200, 0x46c500455a011aa801b548500a8008d3a008a140234100228109c10000f9c807d3884a070005cd4011994023310022610000c001193402325003e490000900088f40231d000a390980700118500230800460c008c1001181001101004600, 0x8b3400764800ec500453c012a740004e004a9a00452c012a542a04a004292007d1c012a3400046004a8a00050c008a0803b3900fe6e0204da1481b004931007e4a00bc7401285001109004a1000941801282002502004a00, 0x22b500456203fa480814885209000451a008a28011448000880044da0089a4017310022550044a400f9440002800223e0024740088500110800220c00441000881801102002200, 0x8b3801f668000cc007d94008b18007610036be007d7a1602f00215d003eb6007d6a0002d001f590002ae006d54005a7801f49003e8e00451a15823005d41002e4a004c7400885801f0a003e10007c1800f82001f02003e00, 0x3eba0045721582e00115a8022b20045620002c0011468022890044da0089a4017310022550044a400f9440002800223e0024740088500110800220c00441000881801102002200, 0x457a008ae40114a8022910044bc0089740002e00225a0044b20001600232b00425200449c00b9280110a002210009c1400882001102002200, 0xb40941780480400805c00e01001801382c0000500800808800c02001008001008000, 0x115e804eb9009d2a008a440113a80227101c4c400f9580232900024e008c9401385002708004e0c00441401382002702004e00, 0x11668022c900453c008a740004e00229a00452c008a540004a00229200e51c010a2801b43003282020cec0429d43003a00766a010c940088500110900221000441800882001102002200, 0x115e8022b9020d34042a643004c002295004524008a44000480022750044e40089c40003800466e00fcc400895801f2900224e0014940088500110800220c01b41400882001102002200, 0x11670022cd000198008b28011630022c200457c008af40005e0022ba007d6c010ac80115700deaa021d2c008a543104a003e8a005c940138580110a00221000441800882001102002200, 0x87610022c10c4180008af40115d0022b9000170008a54011488022750044e40089c40003800466e005cc400895801f2900224e0014940088500110800220c00441400882001102002200, 0x22c50045820089f80113e80007c0044f40089e40003c0022760044e40089b8025350036660064c401f9280110a00520e00441800882001102002200, 0x540d41900480500805c00e0140181180280500401400601400801480c0000100a000, 0x11568052a900450a008a04017350052650044c200f93401b2480023d006c720148500290800520c00a41001481001101005200, 0x8b38011668000cc004594008b18011628000c4004584008af80115d0022b6001d64000ab80195500229e00453a19827001d4100326201c4940148580110a00221000441800882001102002200, 0x22ca004592198320011628022c200458200030000b590022ae00453a008a680114c800098001d1400da180113b0022720044dc00f9a80113300026201c4940088500110800220e00441800882001102002200, 0x22a600454a000290011510022a1000140008a780114d002296004524008a3801f4500228600750400b9280110900221000441800882001102002200, 0x580d41900480600805e00e0180181200280600401600601800800880c0000100c000, 0x11568022a900450a008a04017350022650044c200a9340112480023d0044720088500110800220c00441000881001101002200, 0x715680e2a901c50a038a040713280e262005cc20101800172680064901c46c0388d40201a00e23201c4620100c00710a00e21001c4180388200170100e200, 0x4c0900180d00301800020e, 0xb40c00200d00401800020e, 0x5411002811005020000202, 0x5811003011006020000202, 0x80d001018003e0e, 0x1a81343700900e0100d801c0380300300500e00800400c0380103400100e000, 0x220e, 0x40d80081903801e00420a, 0x1d82a03a0400720600e00a00081200101c00460e, 0x20740f40d80081903c026003e0a, 0xf00d00081800101c003e0e, 0x209c0fc1180082103e032004a0a, 0xf81100082000101c00220e, 0x20cc1041680082b040042003e0a, 0x1001600082a00101c00220e, 0x81100102000220e, 0x2101544400901001010c01c0400300400501000800400c04001034001010000, 0x4e0e, 0x40e80081b04502a00220a, 0x120550240a42400480900808e00e02401800882c0d00501200811800c04801035001012000, 0x8a0700040d00481500102800220e, 0x41380082304903600220a, 0x1241200082200102800220e, 0x41980082d04a04600220a, 0x1281700082c00102800220e, 0x40b80081600902a00220a, 0x209c0041282582304c03a00220a, 0x1301300082400103800220e, 0x20cc0041782682d04e04a00220a, 0x1381800082e00103800220e, 0x81f00103c00220a, 0x2381d44f00901401001401c050030430050140080d800c05001001001014000, 0x520e, 0x41980083105004e00220a, 0x1401900083000104c00220a, 0x82900105000220a, 0x2401d44f00901601001801c058030440050160080dc00c05801001001016000, 0x220e, 0x101e00260e, 0xa60a81481002881200101c002a0e, 0x5602b0120551540942c00480c0080ae00e03001800b82c0200501800810800c06001054001018000, 0xbb1401760807e9d00fd3200b9d80113a81a074005ce400b9b801735002e66005cc400b93401725018048004c7200b8500170800e20e005c1800b82001702002e00, 0x1580d80081500c028002e0e, 0x102400220e, 0x459c008b34000660022ca00458c008b14000620022c200457c008af40005e0022ba007d6c008ad40005a0022b200055c008ab4000560022aa005c940088580110a00221000441800882001102002200, 0x10660020c40041780082d00105600220a, 0x455a008aa8011548000a800450a008a0801140800080005cd4008994011310022610000c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x10540020800040c00081200101c00220e, 0x2c83300104e00320a, 0xb80a80041002d81205a01c00360e, 0x83305d062003a0a, 0x20a81801002f81205e01c00220e, 0x3081b05401c00220a, 0x458a00fb040114e804a990044ec00f9d46203a004272007cdc00f9b400036003e6a0054cc008988017250aa048004c7400f85001f0800020e007c1800f82001f02003e00, 0xfae40115a8036b1009522008a340114480466d0044d200b98801f2a803e52007ca20001400152700223e004c7400f85001f08003e0c007c1001c81801f02003e00, 0xa01d04602400220a, 0x458a008b040114e8022990044ec0089d40003a002272007cdc0109a801133002262005c940088500110800020e00441800882001102002200, 0x114f80229b00452e008a4c01147803e8b00450e00ea0c0113b8022730044de0129ac01b33803263008cae00f94c01127802e4b0080942b01240151f80263b0044263200480110881a01000a41e3180380110681a00c008c161680280110481a00800440e30801801f0281a0040044060480080010081a000, 0x8b14011608022bd004572008a740114c8022950045220089d80113a81a0740044e40089c40003800466e0084d4008998017310ac060008cac00f94801127002e4a0044280088400270700220c008c1400882001102002200, 0x22c5004582008a740114c8022760044ea0681d001139003e6e007cd400899801131002e4a0300900088500110800020e00441800882001102002200, 0x459a008b240836280229e00453a0002700114d00229600452a32825001149003e8e00951400da180114100326200fc940088500010900221000441800882001102002200, 0x8b24011628022c100453a008a680114c80009800951400da180113b0022720044dc00f9a80113300326200fc940088500110800360e00441800882001102002200, 0x459c008b34000660022ca00458c008b080115f0022bd198178008ae801f5b003eb200455c008aa80874f003a82005c940008580110a00221000441800882001102002200, 0x8b28011628022c200458200030001f590022ae00453a008a640113b0022720044dc00f9a801133003a62005c940088500110800220e00441800882001102002200, 0x31827057034002202, 0x32027058034002202, 0xe69f01cd36039a5c0734980e68f01cd16039a1c08f418d408201ccee0399cc0733780e66b01ccce04698c6903100e65701cca603993c08b258d004a02247e0700f40731d81c03a01cc263700480730881c01001cc1e3680380730681c00c0244163600280730481c00801cc0e3580180730281c00401cc063380080890081c000, 0x1cd6a039ac40935500e6a91c0150039a340734481268201cd0237820007336812e6a01ccd23881a008b3100e65501cca40399440e02800e64d01cc940448f80731e81c03c01cc740398500730800e60c01cc1004a8180730200e600, 0x1cd6a03aac409b5500e68d01d51204ca0809536813a690224c403a9847203000ea5501d4a40399440e02800ea4d01d4940448f80751e81c03c01d47403a8500750800ea0c01d4100398180750200ea00, 0x7b04f813e9b004d2e00ba4c0134780268b004d0e009a0c76040805e77005ce60179bc01335802e6700bcc63a81840032b8f0055004ca601593c7402680264b004c7e0780f40131d81e03a00ac263e00480130881e010004c1e3d003802f0681e00c004c163c80280170481e008004c0e3b80180130281e004005c063980080130081e000, 0x18af40715c8016b1004d5a050aa402d4a80e291001d12017a1409f40800a75005ce20019b400332800662005cc20781800172b0006550080a80019480712700064d0080980019280132481e048025c7c0158f47101e002639000c2800184000306002e0a000c1000181001301000600, 0x9af40135c8026a9004d2a021a4402f40802675004ce400b9c40f03800266e005cda1301b0075330056651f40c80099580772a8fc054004ca40099380132500263d004c740098500130800260c004c1400982001302002600, 0x3981200301e00260e, 0x3b2400762805e9d00bd34017a5402f47004a8d068118039a180a3428fe08400bce40179b80813690006c001cc400392802f248ea04800bc7a0178e802f0a005e1000bc1801782002f02005e00, 0x9b3401365000ec2004d7a009ad801f5a83e0b401cd5c03aab48105600169e004d24009a380114690408c002d04005928013248ec048004c7a0098e80130a002610004c1800982001302002600, 0x457a008ae40114a8022910044ea0089c4017310ee0600044ac00f9480112700724a1ac0780088500110800220c004c1400882001102002200, 0x22ce00459a420330011650022c600458a418310011610022be00457a0002f00115d003eb600456a0002d0011590002ae00455a0002b001155002656005c940088580110a00221000441800882001102002200, 0x11b14011568036a9008d3a008a1401140803e72005cd403b9a47e034004665008cc40089840003000464d007c920088f40231d000a390980700118500230800460c008c1001181001101004600, 0x459c008b34860660022ca00458c008b14000620022c200457c008af48505e0022ba007d6c008ad40005a0022b200055c008ab4000560022aa01c4940088580110a00221000441800882001102002200, 0x6d9a008af401b5c80369e006d2a00da4801148800090009514040a24800440092820044ea0089c402d310022560094a400d9441a02800364e00249400d85001b0800360c00441400d82001b02003600, 0x459c00db34000660036ca006d8c00db14880620022c2006d7c00daf48705e0022ba007d6c00dad40005a0036b200055c00dab4000560036aa01c49400885801b0a003610006c1800d82001b02003600, 0x459c008b180115e8022ba0045720002e001f590022b120816002eaa80114a8022910044ea0089c403131002256007ca40089441f02800224e0024940088500110800220c00441400882001102002200, 0x100d80201906c01e00260a, 0xf40880140e80281b06d02a002602, 0x16c000137c0022ec002dc0009b2001b5e000eb0004528011a40013441120801ec0c00089500112600e63c, 0xf80880180e80301b06e02a002602, 0x22ce00459a4603300116480229e00453a4582700114d00229600452a45025001149003e8e004514000a1801141002e4a19c0700088500150900221000441800882001102002200, 0x14f80029b00552e00aa4c01547802a8b00050e01ba0c0153b80767300e4de0199ac00133806a630054ae00a94c01527802e4b00809400a8fc02b1d8e40390054264800480150882001000541e4780380330682000c0054164700280150482000800e40e4680180150282000400540628800800100820000, 0xaab401555002aa924815000aa140154100668124410000b9a801532802a620054c208018008b290112511a00a000a93401525002a4904009000a8f40151d00023904007000a85001508002a0c00541000a81001501002a00, 0x8b140a560802abd005572008a7404b4c802a9500ed220089d80153a8000740054e400a9c410038002a6e0084d400a99801731002a560054a400a9380172500ea3900542800a84002707002a0c00541400a82001502002a00, 0x455a008aa8011549280a800450a008a0801140926080005cd4008994011310022610000c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x14f80029b00552e00aa4c01547802a8b00050e01ba0c0153b80767300e4de0129ac001338092630054ae00a94c01527802e4b25409400a8fc02b1d8de03a0054264c80480150882201000541e4c00380250682200c0054164b80280150482200800e40e4b00180150282200400540629000800100822000, 0xaab401555002aa926815000aa1401541004a8104410000b9a801532802a620054c2488180093290132511a40a000a93401525002a4904409000a8f40151d00023904407000a85001508002a0c00541000a81001501002a00, 0x459a000b24001628002c100453c012a740004e004a9a0095320882600114b00969200e51c012a28001430032820054ec01d9c803937004a6a0094cc02498803f2500e63a00942801484802508002a0e00941801282002502004a00, 0x455a008aa8011549380a800450a008a0801140800080005cd40089940113100226126c0c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x14f80029b007d2e00fa4c01f47803e8b00050e02ea0c01f3b80767300e4de0199ac00133806a63007cae00f94c01f27802e4b27409400a8fc0131d8e003a007c2650804801f08824010007c1e5000380330682400c007c164f802801f04824008007c0e4f001801f02824004007c0629800800100824000, 0xaab401555003ea904815000fa140154100668126810000b9a801f32802a620054c2490180093290136511a80a000a93401525003e4904809000a8f40151d00023904807000a85001508002a0c00541000a81001f01002a00, 0x459c00fb3400066003eca007d92090320011630002c200457c052ae801f5b003eb200055c00eaa80014f00029a007d2c00fa4801f47003e8a007d0c02ea080172500e63a00442c00f85001509003e10007c1800f82001f02003e00, 0x455a008aa8011548000a800450a008a0801140946080005cd4008994011310022612880c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x5d5a00baa80175493a0a8005d0a00ba0803f4092a080005cda00b9a801732802e62005cc2010180097290056511c40a000b93401725002e4900809000b8f40171d00e23900807000b85001708002e0c005c1000b81001701002e00, 0x13c0a82581004681200301c002a0e, 0x4f82a0970401480601b00a00201200401c002a0e, 0x5002a08f0400da0700140c0028120a501c002a06, 0x4c82c0900440dc0700180d0030140a601c002a02, 0xbaf40175c807e95005d2200b9780172e80405c005cb400b9640202c002e56005ca40389380172680404c005c9400b8e40170a002e10005c1400b82001702002e00, 0xe2ce01c59a5403300176480e2c1029d5201fa780714e80409c01c534002a5801749002e8e01c514038a180714280408401c50401e9d80073500e266011cca5381900712680e24a027c720388500170900e21001c4180388200710200e200, 0x38b340a95a802ead01c554038aa4aa05400e28a011d125382200714280e28200fd020102000713680e26a01c4ca0389880173080406000bca200b93407125005a492a40900388f40711d00e2390080700388500710800e20c01c4100388100170100e200, 0x2ece01c59a0103300716500e2c601c58a56031001761000abe005d7400bad80715900e2ae01c55a0102b00715500e29a00152c005a280714300b6852ac1080539840712680e24a02847200b8580710a00e21001c4180388200710200e200, 0x38b380715900b6b12ac160038ab407155002ea9008150054a340174280e28201c5025702000713680e26a01c4ca03898801730804060004ca200b93407125005a492b40900388f40711d00e2390080700388500710800e20c01c4100388100170100e200, 0x5d6a00bac401746807e89005cda00b9a401732802e62005c8c00b91402022002e42005c820101000171f00063a004c720780e00170a002e10005c1800b81801702002e00, 0x1302682604a2bc07a5900481300816200e04c01858002813004002e0700800c09801054001026000, 0xbaf40175c807e95005d2200b9d401738802e65005cc400b9580172900e24e02a49a59813001725002e391cc07000b85001708002e0c005c1400b82001702002e00, 0x2ece005d9a5b033001765007ec6005d8a5a831001761002ebe005d7a0102f00175d002eb6005d6a0102d00175900e2ae005d5a0102b00175500565602acaa5a015001726802e4a004c7200b8580170a002e10005c1800b82001702002e00, 0x1cb140175e802ead005d5400baa4b805400d29d005d2a00ba1401741007e812dc1000159c80ab38968070005cda00b9a801732802e62005cc2010180003290056511d00a000b93401725002e4900809000b8f40171d000a391e007000b85001708002e0c005c1000b81001701002e00, 0x7166800ec9001d8a01fa7803f4e80409c00fd3401fa580694a974094005d2400ba3803f4680408c00fd14038a1807141002e72005cdc0569b4b9036000e6200fc9a01f9280071d005e391d407001f85001709007e1000fc1801f82003f02007e00, 0xbad401758802e9e005d24056a44b9048002e8d005d1401fa2402044002e75005cda00b9a401732802e62005caa00b94801728804050005c9200b8f80091d002e392ec07000b85001708002e0c005c1000b81801702002e00, 0x1767002ecd00819800bb2807163000ec2005d7c01caf4bd05e002eba005d6c00bad40205a002eb201c55c038aa800b4f002e92005d1c057a34bc046001682005c9a00b92800b1d0026391d807000b8580170a002e10005c1800b82001702002e00, 0xbb180175d015eb92f017000bad401759002eb100816000ba3403f44802e75005cda00b9a401732802e62005caa00b94801728804050004c9200b8f80091d002e392f807000b85001708002e0c005c1000b81801702002e00, 0x7902485a03a2fc0726080481400818000e05001858002814004002e0700800c0a001042001028000, 0xbad401758802e8d00fd1200b9b401734802e650500c800b9880172a802e51004c9200b8f80711d00463930807000b85001708002e0c005c1000b81801702002e00, 0x1767002ecd31419800bb2803f63002ec500818800bb080175f002ebd00817800bae80175b002eb530c16800bac807157002ead00815800baa80173b0162753100e800b9a801726802e4a005c7200b8580170a002e10005c1800b82001702002e00, 0x6303340055e80e2b9005d34058a64c404c007e9500fd2401fa4402048002e8e00f50401f9d403f39002e710080e00349b803f32807e62005cac01f94807127000a4a00bc7201f85003f08007e0c005c1401f82003f02007e00, 0x1767002ecd00819800bb2803f63002ec532418800bb080175f002ebd00817800bae80175b002eb531c16800bac807157002ead00815800baa80174b00de9532012800ba2801726802e4a005c7200b8580170a002e10005c1800b82001702002e00, 0x6503380176100dec132018000baf40175d002eb900817000bad800555000a9501c52200b9d401739002e710080e001c9b801732802e62005cac00b94807127000a4a004c7200b85001708002e0c005c1400b82001702002e00, 0x38b1407160807e7e00fcfa0101f003f3d007e790080f001f9d801739002e6e00fcd403899807131007e4d00fc940178e403f0a002e0e00fc1801f82003f02007e00, 0x1503682a06a1e80a26580481500818000e054018588028150040ae00605400800b80c0200102a000, 0x5d5a00baa401742802e81005cda00b9a801732802e61004ca200b9340172480e23d01c47200b85001708002e0c005c1000b81003f01002e00, 0xbb38071668040cc01c59401fb18071628040c401c584022af80175d002eb6001d64038ab80a9569980ac005d54038a780714e99a09c01c5040389880712680e24a027c7200b8580710a00e21001c4180388200710200e200, 0x38b280716499a0c801c58a038b08017608040c032817c005ac80715700e29d01c53401fa640204c18c096001d14038a180053b002e72005cdc0019a80173300e262029cc26701800712680e24a1ec07203885007108002e0e01c4180388200710200e200, 0xba98017528040a4005d4400ba840205000e29e01c53400ba5801749002e8e005d14038a1807141002e4d005c940098e401709002e10005c1800b82001702002e00, 0x1603682c06a1f00a26580481600818200e058018590028160040b000605800800b80c0200102c000, 0x5d5a00baa403f42807e81005cda00b9a801732802e6100aca200b9340172480e23d01c47200b85001708002e0c005c1000b81001701002e00, 0x3ba7c0774d80ee9701dd2603ba3c0b34580ee8701dd0603b9dc0773980ee6f02dcd603b99c07731816a5701dca603b93c1702680ee4b05c09403b8fc0b31d9a003901dc266a00480770882e01002e41e6980380770682e00c01dc166900280770482e00801dc0e6880180b30282e00401dc066780080770082e000, 0x775a8176b1005d5a00baa40bb4680ee89005d0a01fa0401736802e6a01dcd20b81a001732802e62005cc20101800b52a802651005c9a00b9240771f002e3d05c07800b8e80711c804038005c2800b84001706002e0801dc0c00b81001701002e00, 0x1dd7a03bae40774a80ee9101dcea03b9c80773882e07001dcca03b9880772b017a5201dc9c03b9341702600ee4a02cc7203b8500770800ee0c008c1403b8200770200ee00, 0x606c04c0d0018190d101e002e0a, 0x2ec5005d8201fa740434c802e760054ea0801d001739002e6e005cda0101b001735002e6602fcca6a819001731002a5602acaa6b015001726802e4a004c7200b8500170800e20e005c1800b82001702002e00, 0x46c5005d5a00baa8017549b00a801553a00ba1401741007e8135c1000099c801736802e6a005cca00b98801730804060004ca200b93401725002e4900809000b8f40171d000a391e007000b85001708002e0c005c1000b81001701002e00, 0x1562802abd00455a00aaa801f549b40a800553a01ca5401142802a820095026c820001539002a713580e000b9a802332802a620054c208018002b2900ea511f40a000a93401525003e4900009000a8f40151d000a3909807000a85001508002a0c00541000a81001101002a00, 0x61af40715c81829501c5220389d40173880e2650100c80389880172b00e25201c49c03892802324984048004c720388500710800e20c005c140388200710200e200, 0x17668086c900fd3c021a740204e00869a010d2c008a541b04a002e92005d1c021a280714301768536c10800ba080433b018a753700e80219a80432680864a010c720218500c309008610010c1802182004302008600, 0x55e802eb9031d3201fa5403f49007e9100812001f9d403f39002e710080e000a9b803f32807e62005cac01f94801727000a4a004c7201f85003f08007e0c03041401f82003f02007e00, 0x1767002ecd00819800bb2803f630086c2005d7c008af42005e002eba005d6c00bac80715700eead37415800baa80174b00229537812800ba2801726802e4a004c720608580170a002e10005c1800b82001702002e00, 0x6f60802ebd005d7400bae40205c000a9500fd2200b9d401739002e710080e000a9b801732802e62005cac00b94801727000a4a004c7200b85001708002e0c030c1400b82001702002e00, 0x8ad40115880228d0045120089b4011349a4064005cc400895401f2880223e008c740088500110800220c00441000b81801102002200, 0x11670032cd38019800cb28011630032c500018800cb080115f0032bd00017800cae80395b0032b537c168008ac8001570032ad00015800caa80c73a80726a005c940088580190a00321000641800c82001902003200, 0x22cd00458a008b040114e80229a00453200026001149018a91370120008a38019410022760044e40089c41b03800226e0094d400d9980053100aa5600fc940088500110800520e00441800882001102002200, 0x116700decd000198037b280116300dec538818800cb080115f00debd000178037ae801f5b00deb5384168008ac80015700dead000158037aa806f4a81928a005c9400885806f0a00de1001bc1803782006f0200de00, 0x22ce00458a008b08011608000c0004574008ae4de05c0022b6007554008a740114c8022760044e40089c42003800226e007cd400899800531004656005c940088500110800220e00441800882001102002200, 0xa09c054130028230d3036002e02, 0x4580002ef80045e800bb200116200229c005d30002a50017481c60800044e80389c00113200ee4c, 0xc09c058130030230d4036002e02, 0x22cd004592008a780114d00229600452a06825001149003e8e004514000a1801141002e4a33c0900088500110900221000441800882001102002200, 0x115e80a6b9007d62008a5402148804a89008cea0109c407d36802e6202ccc268018001f2b003e550000a800f9480152700264a022c7c00f85001f08003e0c00441400f82001f02003e00, 0x459a008b240116080229e00453a0002700114d002296004524008a38021450036860065040659d80253500366600fc940088500290900221000441800882001102002200, 0x455a008aa8011549ca0a800450a008a0801140800080005cd4008994011310022610000c000893401125003e493900900088f40111d0002390000700088500110800220c00441000881001101002200, 0x459c008b34000660022ca00458c008b080115f0022ba00456c029ac801157003aaa004534066a5801f45002286005c940088580110a00221000441800882001102002200, 0x455a008aa8011548000a800450a008a08011409ce080005cd4008994011310022610000c000893401125003e493980900088f40111d0002390000700088500110800220c00441000881001101002200, 0x3440a00181200301c00220e, 0x1681800401c00220e, 0x34c12002820005024002206, 0x35012003022006028002202, 0x794f9de09e01e53603ca5c0794980f28f03451603ca1c079419d608201e4ee03c9cc0d13780f26b01e4ce0c01940793183006201e4ae06894c0792780f24b3a809403c8fc0cf1d9d203a01e4267800480790883001001e41e7700380790683000c01e4167680280790483000801e40e7600180d10283000401e40674000807900830000, 0x23b38055669e60cc01e56a00eac404755009aa93c8150023a340474500f289060110023a140474100f26d01c4d40239a4a7034008e62034caa03c944047250092493c409003c8f80471e83003c011c7402385004708008e0c011c1003c81804702008e00, 0x3cb380796280f2c101e55403ca740794d00f29906013003ca140794100f27601e4e403c9b80cf3500f26601e4ca0c01900793100f24a01e47403c8500790800360e01e41803c8200790200f200, 0x1e80cc00c138018210ec03200320a, 0x3b2404963000ec53dc188024a780254e82209c01252a024a340494500028603550a7a82100393900fe6e035cda7b01b004932809262001c940038e80490a00921001241802482004902009200, 0x8ad401f5880fe92035d227b02400114680728a00951208822004d3a80226d012cd200b9880392a807252007ca200014007325002a3e00247401c8500390800720c00e41000881803902007200, 0x1f00cc010138020210ed03200320a, 0x115e8022b9021532008a54011488022750044e40089c40003800466e00fcc40089580212900224e0014940088500110800220c01b41400882001102002200, 0x7c833005046003202, 0x19668032ca00658c008b1421062000eb200055c03cab4fa05600329e00453a7d8270001410032650064c40389280190a00321000641800c82001902003200, 0x22ad021d54014aa4fc0541dc08c00450a008a04017350052650044c201493401f2480223d006c720148500290800520c00a41001481001901005200, 0x459c00cb34000660032ca00458c00cb14000620032c200457c00cae801f5b0022b200055c00cab4000560032aa005c940148580190a00321000641800c82001902003200, 0x453e008a6cfe04c802297004526008a3cfd0458022870005060089dc0113980226f0124d67b81a8055339e60660064c601195c0212980224f00f4965401280351f805a3b0044267f80480110883201000a41e7c80380110683200c009c167c00280110483200800440e7a0018049028320040044062c800800100832000, 0x22ce00659a0c8330019650022c600658a0c8310019610022be006574024ad8011590002ae00655a0c82b0019550032990124d4023998079329de06401c4940148580190a00321000641800c82001902003200, 0x22ce00459a0c8330011650022c9000190008b18011610022c13ec180008af80115d0022b6002d64008ab805b5500229e004534008a642104c002296004524008a3801f450022860005040039a80553300e24a00442c0088500110900221000441800882001102002200, 0xc0cc0181688002b0f0046003202, 0x22c600458a8183100116080229d0045327402000113b0022754080e80089c801f3700226d4040d80089a800133002262005c940088500110800360e00441800882001102002200, 0xda7d0704e80369b006d2e00da4c01b4780168b00050e00ea0c01b3b803673006cde0129ac01b33808e633c40c402a95c0532980364f00f4965481280011f805e3b01642684004801b08834010006c1e83003801b0683400c015c1682802801b04834008006c0e82001802502834004006c062d000800100834000, 0x6d9a00dab401b550036a9428150023a28079449d2088006d0a00da0801b4083408001c4d400d99401b310036614240c000d93401b25004a4906809000d8f401b1d00023906807000d85001b0800360c006c1000d81001b01003600, 0x62cd00457a005ae401b5a8016b1006d2a012a4401b46804a890125040119d40213880aa6d014cd201698801f2b004a550000a80129480252883405000049c0099280331f005e3a0094280128400250600220a00941000d81802502004a00, 0x229f004536008a5c0114980228f036d16008a1c01d418022770044e60089bc025358036670064c602a95c0212980364f010c960101280d91f805e3b0044268700480110883601000a41e8680380110683600c0044168600280110483600800440e8580180db028360040044062d800800100836000, 0x6d9a008ab401b550036a943c150023a28079449d4088006d0a00da080114083608001c4d400d99401b3100226106c0c000893401b25004a4942409000d8f401b1d00023906c07000d85001b0800360c006c1000d81001101003600, 0x11628022c100457a008ae40114e80229900452a008a440113b0022750000e80089c801138836070008cdc0109a801b33002e620154ac0109480112700864a0044280088400110700220c009c1400882001102002200, 0xda7d1304e80369b006d2e00da4c01b4780168b00050e00ea0c01b3b803673006cde0129ac01b33809a633c80c401195c0532980364f00f4965501280011f805e3b0164268a004801b08838010006c1e89003801b0683800c015c1688802801b04838008006c0e88001802502838004006c062e000800100838000, 0x6d9a00dab401b550036a9070150023a28079449d6088006d0a00da0801b4083808001c4d400d99401b3100366143c0c000d93401b25004a4942809000d8f401b1d00023907007000d85001b0800360c006c1000d81001b01003600, 0x459c00db34000660036ca006d920e032001b630036c5078188008b080115f0022ba00456c005ac800157003aaa006d3c06ea751504e00369a006d2c00da4801b4700168a008d0c00ea0804d3100e24a00442c00d85005909003610006c1800d82001b02003600, 0x455a008aa8011548000a800450a008a0801140800080005cd40089940113100226145c0c000893401125003e494580900088f40111d0002390000700088500110800220c00441000881001101002200, 0x8802a0ec0440060804600c08581200301c00360e, 0x8882a0ed0440080804640c08281200401c00360e, 0x2240b04341108301a005028003602, 0x1b668036ca002d74000ad801b5501baa9454150000a2801b44a34088006d0400da041e04000e26a006cc400d92803124a0e048006c7a00d8e801b0a003610006c1800d82001b02003600, 0x7802e00605821c0884200d00301411b01c003602, 0x7b4fa4609d01ed3603da5c07b4981be8f01ed1603da1c1d04280f68307410403d9dc07b3980f66f0384d603d99c07b31a3e06201ecae06f94c07b2780f64b47809403d8fc0df1da3a03a01ec2692004807b0883a01001ec1e91003807b0683a00c01ec1690802807b0483a00801ec0e9000180df0283a00401ec068e000807b0083a000, 0x11b3805b66a4e0cc016d6a02dac807b5883a0b0016d5a02daa807b46803289016d0402da052604000f66d01c4d402d9a4ab03400b662038caa03d94405b2500ba4949409003d8f805b1e83a03c016c7402d85005b0800b60c016c1003d81805b0200b600, 0x3db3407b6500f6c907419003db1407b5680f6aa01ed3c03da6807b4b00f69201ed1c06fa2807b4300f68507410803da0807b3100f64a01ec7403d8500110900f61001ec1803d82007b0200f600, 0x60cc4a01880182b120042003a0a, 0x2eb3801f668240cc001d8402eaf405d5a80bab200055c071ab52905600169e01753a9582700c949003e8e03951a95023005d4280ba82002c940058e805d0a00ba1001741802e82005d0200ba00, 0xfae80e55ca540b800456a00fac801f588240b000451a012a2405b3a80226d0294d200b98801f2a803e52007ca200014007325002a3e00247400f85001f08003e0c007c1000881801f02003e00, 0x80cc4b01880202b121042003a0a, 0x11608022bd004572008a54011488022750044e40089c40003800466e005cc40089580532900224e0014940088500110800220c00441400882001102002200, 0xa0cc0141689682b122046003a02, 0x1d670036cd07019800eb1401d61000eb200055c03dab52e05601ce9e00753a97827001d42803a820004c403892801d0a003a1000741800e82001d02003a00, 0x6d3e00da6d1304d003697006d2600da3c05d45a5608a008d0e93821801d41803677006ce600d9bd300358036670004c601195c0532980364f0014965601280371f80623b01642699004801b0883c010006c1e98803801b0683c00c015c1696002801b0483c008006c0e94001805d0283c004006c062e80080010083c000, 0x36cd039d9400db252f0640022c5006d8400db041c0600016b2008d5c00da7801b4e83c09c006d34008a640004c003696006d2400da38007450036860135040089d80113900226e0094d400d9980013100e24a006c2800d84801b0800220e006c1800d82001b02003600, 0x36ce00759a0f033001d650036c600758a0f031001d610036be00757402ead801b590002ae00755a0f02b001d55003a9a01751402da1807b42a4608401c49402c85801d0a003a1000741800e82001d02003a00, 0x9903300605a003a02, 0x2480b400455a008aa401142810682004502998200017350022650044c202c93401f2480223d0044720088500110800220c00441000881001d01002200, 0x22c50045828e02a00114f00229d4d8138008a640113b0022754d40e80089c801f3700226d4d00d80089a800133002262005c940088500110800220e00441800882001102002200, 0x8a7d3a04f00229b00452e008a4c01147803e8b00450e02da0d250410022770044e60089bc007358002670064c601195c0212980224f0014965681280011f80263b0044269d80480110883e01000a41e9c80380110683e00c009c169c00280110483e00800440e9b801801f0283e0040044062f00080010083e000, 0x459c02dac807b58a3a0b000455a008aa80115483e0a800450a008a0801140a7a08001c4d4008994011310022614f00c000893401125003e4907c0900088f40111d00023907c0700088500110800220c00441000881001101002200, 0x5ace00457a00fae40115a803eb1017554008a540074880228d001d120119d40213880466d0084d201698801f2b003e550000a800f94801f2883e05000049c0099280151f00263a007c2800f84001f0600220a007c1000881801f02003e00, 0x229f004536008a5c0114980228f007d16008a1c01d418022770044e60089bc0e9358036670064c601195c0212980224f005c960101280391f80263b004426a080480110884001000a41ea000380110684000c009c169f80280110484000800440e9f001801f028400040044062f800800100840000, 0x459c02dac807b58a3c0b000455a008aa8011548400a800450a008a0801140a8408001c4d4008994011310022610800c000893401125003e494f00900088f40111d0002390800700088500110800220c00441000881001101002200, 0x11628022c100457a008ae40114e80229900452a008a440113b0022750000e80089c801138840070008cdc0109a801133002e62008cac01094801127002e4a0044280088400270700220c009c1400882001102002200, 0x8a7cfe04f00229b00452e008a4c01147803e8b00450e02da0d260410022770044e60089bc007358002670064c601195c0212980224f0014965701280011f80263b004426a300480110884201000a41ea280380110684200c009c16a200280110484200800440ea1801801f0284200400440630000800100842000, 0x459c02dac807b58a3e0b000455a008aa8011548420a800450a008a080114084208001c4d4008994011310022615080c000893401125003e494f40900088f40111d0002390840700088500110800220c00441000881001101002200, 0x459c008b34190660022c900458c008b15470620022c1016d54008a780114e80009c004534008a642104c002296004524008a38007450002860065040089d80113900226e001cd402a9980193100e24a0044280148480110800520e00441800882001102002200, 0x9002c0030542860805200c09f01200301c00220e, 0x9082c0040542880805240c09c01200401c00220e, 0x9102e0050582800884e40d00281414a01c002202, 0x11668022ca001d74000ad8011550022a951c150000a2801144a96088004504008a041904000e26a0044c400892802d24a7404800447a0088e80110a00221000441800882001102002200, 0x28c0b05041109d81a006028002202, 0x2011004020003e0e, 0x281700502c003e02, 0x5b00007df0005b8001f64000eb000451800fa2001122002240, 0x301700602c003e02, 0xc0e80181914c02600720a, 0x14c0340060602bc0a0a681200301c00020e, 0x181100302000220e, 0xa700e95000904401053c01c1100300400504400800c00c11001034001044000, 0x4e0e, 0xc0e80181b15102a00220a, 0x5440e00181a00302800220e, 0xc1380182315203600220a, 0x5481200182200302800220e, 0xc1980182d15304600220a, 0x54c1700182c00302800220e, 0x181700302c00220a, 0x2aa0cc00c1380182515403a00220a, 0x5501300182400303800220e, 0x60cc55c1880182f15604a00220a, 0x5581800182e00303800220e, 0x181f00303c00220a, 0x5881495800904601001401c1180314f0050460080d800c11801003001046000, 0x520e, 0xc1980183115904e00220a, 0x5641900183000304c00220a, 0x182900305000220a, 0x5901495800904801001801c120031500050480080dc00c12001003001048000, 0x220e, 0x22c501bd82008a740194c80227600e4e400a9b80113500026600e4ca00019003931002e4a004c7201c85003908003e0e00e41801c82003902007200, 0x22ad006d5200da140114080e26a005cd25981a00113280e2620044c2ad01800152a80224d004c920008f40011d0002390000700008500010800020c00041000081001f01000200, 0x303600420a, 0x2ba0a85701000181215b01c00460e, 0x30660060c400c1780182d00305600220a, 0x305400608000c0c00181200301c00220e, 0x182715e046004a0a, 0x304400220e, 0x183315f05a003e0a, 0x305800220e, 0x220a, 0x8b1401160810abd00453a008a640854a8022760044ea0001d00113900466e0044d400099803931004252005c9400885001108003e0e00441800882001102002200, 0x22bd004572008a54011488022750044e40089c40003800466e005cc40089580212900224e005c940088500110800220c008c1400882001102002200, 0x8b3801166ac00cc004592008a780114e80009c004534008a580114900228e004514000a180194100726a005c9400885001f0900221000441800882001102002200, 0x459a008b140116080229d004534008a640004c00229200451c00ca080113b0022720044dc0129a801b3301d66200fc940088500110800360e00441800882001102002200, 0x8b38011668000cc004594008b1801162ac20c4004584008af80115d0022b6004564000ab806f55003e8a005c9400a8580110a00221000441800882001102002200, 0x459c008b14011610022c1000180008ae80115b003aaa00453a008a640113b0022720044dc00f9a80113301da62005c940088500110800220e00441800882001102002200, 0x2202, 0x2202, 0x22ad029552008a1404b40802e6a02fcd26a81a001132802a620054c208018007528802a4d007c9200a8f40151d00023900007000a85001508002a0c00541000a81001101002a00, 0xfa9f01f53603ea5c0ef4980fa8f01f51603ea1c07d41aca08201f4ee0789cc07d3780fa6b01f4ce03e98d6403101de5701f4a603e93c2502681de4b09409403e8fc07d1dac603a01f426b4004807d0884a01001f41eb3803807d0684a00c01f416b300280ef0484a00801f40e1c001807d0284a00401f406b1000807d0084a000, 0xfb1407d5e803eb9007d54012a7407d4a804a91007d0400f9d401f3901de710940e00099a801f32803e620054ac03e94807d27003e4d09409800f92801f1d0006395a407000f85001f08003e0c01f41400f82001f02003e00, 0x7d5e80fab901f55403ea5407d4880fa8201f4ea03e9c80ef3884a07001f4ca03e98807d2b00fa5201f49c03e9342502600fa4a01f47403e85007d0800fa0c008c1403e82007d0200fa00, 0x403600420a, 0x8ab402754804e85004502b301d0071350022650044c200893402324804e3d00047201385002708004e0c009c1001381002101004e00, 0x459a010b240114f00429d000138010a680114b004295000128010a4801f4700428d000118010a2800143002282010c940108500110900421000841801082002102004200, 0x22c900458a008b040114e80229a00453200026008349004a8a006d0c0089d80113900226e007cd400899801931004a5600fc940088500110800da0e00441800882001102002200, 0x459c010b34000660042ca00458c010b080115f0042bd000178010ae801f5b0042b5000168010ac8001570022aa005c940138580210a00421000841801082002102004200, 0x22ca00458a008b08011608000c0021d7400fac80115700229d0045320089d80113900226e007cd400899801d31003e56005c940088500110800220e00441800882001102002200, 0x141380282516703a004202, 0x181380302516803a004202, 0x22ce00459ab603300116480229e00453ab582700114d00229600452400fa380114500028600450ab50210011412c4050005c940088500230900221000441800882001102002200, 0x8d3e011a6c0234bae0095008d2600fa3c01f45804687016d060119dd6f03a80467300e4de0129ac05533809a63008cae00f94d6902900464f005c963c01280151f80263b015426b900480230884c010008c1eb880380230684c00c008c16b700280230484c008008c0ead801801f0284c004008c06b680080050084c000, 0x46c5008d5a011aa802354ae80a8008d3a011a14023410046815cc10000f9c807d38ac6070005cd4011994023310046610980c001193402325003e490980900118f40231d000a390980700118500230800460c008c1001181002301004600, 0xac500456a00eac40235680b6a900153a00da340194480aa850135020019c802336800a6a005cd20101a002332800a62005cc23c01800152a80265100549a0099240011f000a3d0000780028e80051c84c03800142800284000506000a0800440c00281002301000a00, 0x114f80229b00452e008a4c01147803e8b00450e02da0c0113baec0750044e601c9bc0253580aa670064c601195c0212980224f005c966b81280151f80263b004426bc00480110884e01000441ebb80380110684e00c009c16ba80280110484e00800440eae001801f0284e0040044061d00080f30084e000, 0x46c500455a011aa802354af20a8008d3a011a140234100228109c10000f9c807d38ac8070005cd40119940233100226109c0c001193402325003e4909c0900088f40231d000a395cc0700118500230800460c008c1001181001101004600, 0x8b34011648022c5004582008a780114e80009c004534008a642704c00229600452a1502500114900728e00951400da18019410022760214eabd01d00113900226e0094d402a99801931007e4a0044280088480110800520e00441800882001102002200, 0x455a008aa801154af80a800450a008a0801140800080005cd4008994011310022610000c000893401125003e490000900088f40111d0002395ec0700088500110800220c00441000881001101002200, 0x1b4f80369b006d2ebf025401b49803e8f007d16011a1c01d41803677006ce600d9bc025358036670134c601195c0532980364f005c966c01280151f80263b006c26c0004801b08850010006c1ebf803801b0685000c015c16be802801b04850008006c0eae801801f02850004006c061d80080f500850000, 0x46c5008d5a011aa801b548500a8008d3a00da14023410046815e410000f9c807d38aca070005cd4011994023310036610a00c001193402325003e490a009000d8f40231d000a395d00700118500230800460c008c1001181001b01004600, 0x8b3801b668000cc006d9400db24280640022c600458400daf801b5e8580bc00457400fad801f590022ae00755400da7801b4d00369603dd2ac0825001b4900368e007d14011a1801d41002e4a00442c00d85005909003610006c1800d82001b02003600, 0x455a008aa8011548000a800450a008a0801140b06080005cd4008994011310022610000c000893401125003e490000900088f40111d0002396080700088500110800220c00441000881001101002200, 0x2fa0a85d41000201216e01c00460e, 0x46c5008d54011a740234d004682021502bd020001f390046716100e00029a8023310022610a80c00119340232500463a001472b780e00230a004610008c1801182002302004600, 0x46c5008d84011aa80f754b020a8008d3a011a0801f390046716140e00029a8023310036610b00c00119340232500463a001472b800e00230a004610008c1801182002302004600, 0xbf82a16704c00a0800140c0b881218601c004606, 0xbc02c16804c00c0880180d0b901418701c004602, 0x59a000ad4011568002aa000552c482a00014501aa893d411000da1400141004a810441000389a8011328002620364c2c40180073290146511fc0a000a93400125004a490680900008f40011d0002390000700008500010800020c00041000081001101000200, 0x1029f03f536040a5c0814981028f020516040a1c0f9418102776340ea07e9cc0813785206d03f4d61481a80fb338102630204ae04094c08127815a4b2e40940408fc0f91db1403a020426c780480810885201002041ec700380fd0685200c03e416c600280810485200802040ec58018081028520040204061f00080f900852000, 0x2057a081ae407f5a804a9d01fd2a03fa480fd4885209001fd1a03fa281013a81fa7101fcd200b9880812b00fe550a40a803f9480ff27005e4a00247403f85007f0800fe0c02041403f82007f0200fe00, 0x81628102c102053a040a680fd4c85209802052a040a34081450102760204e40409b80813685206c0204d404099810531015a4a03e4740408500810800360e02041804082008102010200, 0x4b04007df8003be00257a004aec0095c800fb3190062020eb4007d3800fa5001f4602066c, 0x809c6441280202318c036004a0a, 0x3fb340254f00229d09c13801da5403b4900fe8e04051ac90230039410196760094eac981d003b3680766a010c940178e803b0a00761000ec1801d82003b02007600, 0x114f80229b00452e008a4c01147803e8b00450e02da0c0113b8022735d80e40089bc0253580aa670064c601195c01f2980224f001496ca01280151f80263b004426cb80480110885401000a41ecb00380110685400c009c16ca80280110485400800440eaf001801f028540040044061f800800700854000, 0x11628022c100457a008ae40114e81969a004532c982600114a8022920045221382400113b0022750a80e80089c801138800070008cdc0109a801133007e62008cac00f94801127000a4a0044280088400270700220c009c1400882001102002200, 0x8b3400764800ec500453c012a742a04e004a9a00452c012a542a04a004a92007d1c012a342a046004a8a001d0c008a0802539004a6e0204dac681b004931000e4a00bc7401285001109004a1000941801282002502004a00, 0xcb02700504a004a02, 0x1d94003b2598064000ec5001d84c802c800757000e9d001d34003a5400746800e8a00050c03f9c807f37000e62001c940038e80070a000e10001c1800382000702000e00, 0x22ad004552c7025001142802281005cd4008994011310022616640c000893401b2480223d0004720088500110800220c00441000881002501002200, 0x1167000ecd000198003b2801163000ec5000188003b080115f000ebd66c178010ae801f5b000eb5000168003ac800157000ead668158008aa80074f000e9d660138003a0800731000e4a001c740088580070a000e10001c1800382000702000e00, 0x8b34011650022c9000190008b0801f590022ae00453c008a680114b00229200451c00fa280114300b68201c4940088500110900221000441800882001102002200, 0xc0cc65c1880302f18f04a004a02, 0x457a084ae401d54803695006522004a280f944b1408801e50a0089d401938801262005cc25d81800392b00265200049c0049340002600124a02647a0048500090800120c00441400482000902001200, 0x8b140116080229d004532c582200113b002272007cdc0089a800133002262005c940088500110800220e00441800882001102002200, 0x458a008b040115c80229d004532062a5407f450022760044ea0001d00113900726e0084d400899801931007256005c9400885001108004e0e00441800882001102002200, 0x459c008b34000660022ca00458c008b080115f0022ba00456c00fac8011570212aa00453c008a4801147003a82005c940088580110a00221000441800882001102002200, 0x395d0022b5004564008ac40005800fe9200451a008a28011448000880044da0089a801134b3a068005cc400895401129003e510000a00088f80091d0022396700700088500110800220c00441000881801102002200, 0x6301200202200402800220e, 0x5038002202, 0x63c1800302e006038002202, 0x59c000ac80e358a520b000455a000aa801f548240a800051a008a140014100028167c1000389a80113280026200e4c2cf01800732900ea512040a000a93400125003e4907c0900008f40011d0002390000700008500010800020c00041000081001101000200, 0x229f044536086a5da304a80429300451e1582341114585608a043d0e086a0c0113b8022730044de0089ac10d338032630044ae00894c01127815e4b2f00940088fc10b1db4003a004426d280481110885601000a41ed200380110685600c009c16d100280110485600800440ed080180110285600400440620000810b00856000, 0x7d8a00faf401f5d0222b90ac17000fad401f59002295041d2201ca341133a804271007cd200b9880112b003e550ac0a800f9480152700264a00247400f85001f08003e0c00441400f82001f02003e00, 0x11668022ca04459215832010d5e8022b5004564008a780114d002296004524008a380114685608c004514008a1811541015e4a042c740088500110900221000441800882001102002200, 0x80cc6981780202d1a2046003e0a, 0xfb3801b668500cc045d8c00faf401f5d003eb6044d6ad382d00c955019a96007d2ad4025001f46803e8a005c940098e801f0a003e10007c1800f82001f02003e00, 0x1b4f80369b006d2e00da4d7e04900368f007d16011a1c01d41803677006ce600d9bc025358036670134c601195c01f2980364f001496d481280151f80263b016426d6004801b08858010006c1ed5803801b0685800c015c16d5002801b04858008006c0eaf801801f02858004006c0620800800b00858000, 0x1b62819ac2006d82d403000115e8036ba006d721402e001b4e80369900452a008a4401b3b0036750b00e800d9c801138800070008cdc0299a801b33002e62008cac00f94801127000a4a006c2800d8400570700360c00441400d82001b02003600, 0xdb3801f668580cc007d9400db1800b610036be007d7a1602f001f5d003eb6007d6a1602d001f590016ae006d54005a7801f49003e8e04351ad1823005d4100164a004c7400d85801f0a003e10007c1800f82001f02003e00, 0xa0cc6ac1880282f1a404a003e02, 0x1d94005b25980640016c5002d84005af400b5a8016b200055c005a7400b4d32008a002d0c01c9c803937001662002c940058e800b0a001610002c1800582000b02001600, 0x8b24011628022c100453a008a680114c80009800951400da180113b0022720044dc00f9a801133009a6201c4940088500110800220e00441800882001102002200, 0xd603100605e003e02, 0x34a0bc00455a008aa401142802281005cd4008994085310022616b40c00089340112480363d0004720088500110800220c00441000881001f01002200, 0x457a00eae4009590216b168016003dab401b4a8032910065020089d406f38801262005cc25f018001f2b00265200049c0049340002600124a04647a0048500090800120c00441400482000902001200, 0x8b1401160b420b000453a008a640113b0022720054dc0089a800133002262005c940088500110800220e00441800882001102002200, 0x458a008b040115e803eb200453a008a64011488022760044ea0001d001139003e6e0084d400899806f31003e56005c9400885001108004e0e00441800882001102002200, 0x459a008b240116280229e00453a0002700114d002296004524008a38025450036860065040089c80113700326200fc940088500290900221000441800882001102002200, 0x6881700202c00402800220e, 0x6901800282e005038002202, 0x6038002202, 0x281f00503c002202, 0x301f00603c002202, 0x5a04d0b4094d780482d00835c00e0b401801182c0d00505a00853800c1680104600105a000, 0x403a05a0700100c8d801300270700460a, 0x6c00d00201800401c00020e, 0x100e80201b1b102a00460a, 0x6c40e00201a004028003e0e, 0x201700402c004e0a, 0x10138020251b203a00220a, 0x6c813002024004038004e0e, 0x101980202f1b304a004e0a, 0x6cc1800202e00403800220e, 0x201f00403c00220a, 0xd701a9b400905c01001401c1700314f00505c00810c00c1700100400105c000, 0x520e, 0x10198020311b504e00220a, 0x6d41900203000404c00220a, 0x202900405000220a, 0xd781a9b400905e01001801c1780315000505e00811000c1780100400105e000, 0x220e, 0x115e8036b9006d2a008a440113a80227101c4c4011984c2030003e56008ca40009380232680004c008c940118500230800460c00441401182002302004600, 0x455a08daa4027428032810044da0389a80113280e262005cc201018001328802a4d004c920008f40011d0002390000700008500010800020c00041000081001101000200, 0x22bd006d72013a54011488046750044e20329a407131003e56008caa0001500232900024e008c940118500230800460c00441401182002302004600, 0x22b5007d62008a34025448046750044da0109a401731003e55007ca400f94400028002a3e004c7400f85001f08003e0c007c1000881801f02003e00, 0x40660080c40101780202d00405600220a, 0x40540080800100c00201200401c00220e, 0x22cd004592008a780114e80009c004534008a5801149003e8e004514000a180114100227201c4940088500290900221000441800882001102002200, 0x115e804eb9009d3c013a5402749002291000120012a280113a8022710304c400895802529004e4e01349401385002708004e0c00441401382002702004e00, 0x22ce009d9a00033002765004ec6004584008af80115d003eb6006d64000ab801b55004e9201c4940088580270a004e10009c1801382002702004e00, 0x11630022bd004574008ae40005c003eb200452a008a440113a802271030cc400895801f2900224e016c940088500110800220c00441400882001102002200, 0x404e00220a, 0x404c00220a, 0x406600220a, 0x406000220a, 0x4e02, 0x4e02, 0x22ad006d5203ca2401b4280228101c4d405d9a4db034002265006cc40089841b03000224d04749200d8f401b1d00023900007000d85001b0800360c006c1000d81001101003600, 0x23eb900456a00dac40c54e80fe92009522c902400114680728a00451213822007d3880466d0044d200b9880392a807252007ca20001400392700223e00247401c8500390800720c00e41000881803902007200, 0x834f81069b020d2e041a4c08347824a8b020d0e065a0c0833b860075020ce61801c80cb37824e6b032cce09198c0832b824a53020c9e06592c1211f81963b020c26dc004808308860010020c1edb80380830686000c020c16db002808304860008020c0ea9001812502860004020c062480080cb00860000, 0x20d8a041b040834e81069a020d321802600834a810692020cec0419d43003a010672032cdc0939a8083330196620494a404185008308010a0e020c1804182008302010600, 0x8362810ac102153a042a680834c86009802152a042a480c547018e82020cec0429d43003a010a72020cdc0959a80c53301966204a4940428500850801060e02141804282008502010a00, 0x504e002202, 0x8ab401154b6e09c00450a008a040c3350022650044c200f93401f24825a3d0004720088500110800220c00441000881001101002200, 0x459c008b34000660022ca00458c008b14000620022c200457c008af40005e0022ba007d6c010ac8001570032aa010c940088580110a00221000441800882001102002200, 0x22cd004594008b24000640022c2021d7401cac80115700229e004534008a580114900228e007d14008a180ed4100fe6a005c940088500110900221000441800882001102002200, 0x18198030311b804e002202, 0x458a037b0401d5480229d006532094a4401b42802276005ce40029c402038002a6e0044d4000998005328000640014c400295807726800a4a004c720028500050800520e00141800282000502000a00, 0x22c5007d8200fac40114e804a99049524040a340113b003e750a80e80109c801f37003e6d0000d800f9a801533002262007cac0119558402a007e4a004c7400f85001f08004e0e007c1800f82001f02003e00, 0x8af406d5cb6c098009d2a008a440293a8022710304c400f95801b2900024e006c9403685006d0800da0c00441403682006d0200da00, 0x459c008b34000660022ca00458c008b080115f0022ba00456c00fac80115700deaa00453c008a5801f45003a82005c940368580110a00221000441800882001102002200, 0x22bd004574008ae40005c002295004524008a44000480022750044e40089c40003800466e0014c400895801f290022516e80a0008938005250022496e40900088500110800220c00441400882001102002200, 0x504c002202, 0x6e01900303000604c002202, 0xf6b100455a008aa40114280228101c4d403b9a4dd0340022650044c40089842003000224d007c920088f40111d0002390000700088500110800220c00441000881001101002200, 0x262c5007d7400fae5a705c0022b5007d6400dac428058025e9100451a008a2407d3880466d0044d200b98801f2a803e52007ca20001400152700223e00247400f85001f08003e0c007c1000881801f02003e00, 0x874f810e9b021d2e1882540874986209203351e09ca2c0cd43826a83021cee0439cc08737826e6b021cce06698c0872b826e53021c9e06692c1331f819a3b021c26de804808708862010021c1ede00380870686200c021c16dd802808704862008021c0ea9801813702862004021c062500080cd00862000, 0x21d8a043b08087608620c0021d7a043ae80874e810e99021cec0439d43103a010e720334dc09c9a808733019a6204dca404385008708004e0e021c1804382008702010e00, 0x11668022ca021d921883200115e8022ba04c56c037aa80874f00229a021d2c008a543104a002292021d1c09ea2801143019a8204ec940088500870900221000441800882001102002200, 0x14198028311bc04e002202, 0x22c900458a008b041175900229d004534008a640004c01069201a51400da180113b0022720044dc00f9a80113301d66200fc940088500110800da0e00441800882001102002200, 0x6062002202, 0xde831001156804ea9009d0a008a040c1350022650044c200a93401f24827e3d00047201385002708004e0c009c1001381001101004e00, 0x458a00eb0413b5c8022ad006d3a00ca6401940802276005ce40029c402038002a6e006cd4000998005328000640014c400295801126800a4a004c720028500050800220e00141800282000502000a00, 0x22c5007d8209bae80115a80229d009532012a2401b3b003e750b00e80109c801f37003e6d0000d800f9a801533003662007cac0119558502a002e4a004c7400f85001f0800220e007c1800f82001f02003e00, 0xdd83000115e8022b900452a008a440113a802271030cc400f9580112900024e0044940088500110800220c00441400882001102002200, 0x459a008b240116280229e00453a0002700114d002296004524008a38025450036860065040089d80253500326200fc940088500290900221000441800882001102002200, 0x6f01900283000504c002202, 0x604c002202, 0x3029006050002202, 0x280d005018005202, 0x140a8028131be01e003602, 0x37e0806f80a00281200501c000206, 0x140e8028191c0026003602, 0x3820a87000d00281800501c003e06, 0x14138028211c2032002202, 0x7081100282000501c005206, 0x141980282b1c3042005202, 0x70c1600282a00501c002206, 0x2829005050002202, 0x658249b400906401056001c1900304f00506400801800c19001005001064000, 0x2206, 0x22b5006d6200da340114480a28100a4da0089a407131003e55006ca20008f801b1e80003c006c7400d85001b0800360c006c1000881801b02003600, 0x8ab406f5480368d00450a00ca040713500226501c4c401c985c4030002a4d007c920008f40011d0002390000700008500010800020c00041000081001101000200, 0x22bd006d72008a5401148803689006cea0089c401731003e56006caa00015001b2900024e006c9400d85001b0800360c00441400d82001b02003600, 0x455a0a1aa801f54b8a0a800452a008a1402540802e6a00a4ca01098401329003e4d007c9400f92400024002a3d05047200f85001f08003e0c007c1000f81001101003e00, 0x11628022c100453a008a64011488022760044ea0001d001139003e6e0044d400099801131004656005c9400885001108004e0e00441800882001102002200, 0x22ad00a552014a7401142802281005cd4014994029310022610000c00149340532480223d0514720148500290800520c00a41001481001101005200, 0x506600a0c40141780282d005056002202, 0x505400a0800140c00281200501c002206, 0x8b38029668000cc00a594008b18011610052be00457400fad801b590002ae006d54014a6814345005286005c940088580290a00521000a41801482002902005200, 0x1167003ab200455a008aa8011548000a800450a008a04017350022650044c200893401f2480223d0074720088500110800220c00441000881001101002200, 0x5066002202, 0x5064002202, 0x5202, 0x59c000b35c80660002b201ed629702c0011568002aa006d520e02a00014500f2893e811000da14001410022810841000389a8147349980680044ca00098801130b8e0600004aa00893400125005a497180900008f40011d0002390000700008500010800020c00041000081001101000200, 0x115c8022b5004562040a44011468022890044da0089a4017310022550044a400f9440002800223e004c740088500110800220c00441000881801102002200, 0x8b040115e8022b9021532008a54011488022750044e40089c40003800466e005cc400895801f2900224e005c940088500110800220c01b41400882001102002200, 0x114f86609d0045361982680114b80229300451e003a2d9804500028772010c00ca0c0113b8022730044dee501ac011338002637240c401195c0212980224f0114966681280011f805a3b00a426e600480110886601000441ee580380110686600c009c16da80280110486600800440eac801802d0286600400440628000800100866000, 0x8b34011650022c90cc190008b1401161000eb200055c008a780114e86609c004534008a580114900228e001d14073a180194100026201c4940088500290900221000441800882001102002200, 0x8b34011650022c90cc190008b1401161000eb200055c008a780114e86609c004534008a580114900228e002d14008a181494100026201c4940088500110900221000441800882001102002200, 0x6066002202, 0xe60330011568052a900450a008a04017350052650044c200a93401f24802a3d0004720148500290800520c00a41001481001101005200, 0x1670022cd06419800eb24001610002c1724180005ac8001570022ad52c15800da780014e83c09c006534008a580174900728e008d14000a18001428000840005040039a8001330036654680c8038928e302499c0482240720008500110900021000041800082000102000200, 0x1166803ec900456a008a780254d004696007d2ae6825002149003e8e007d1a00023001f45002a86008d040089b40212880064a004c7400f85001109003e10007c1800f82001f02003e00, 0xb803940f8007de0003b2001162003ec0008d78008ad001f4c00226c, 0x22cd004592008af40395900229e004534008a580114a80009400452401ca3802145002286005d040089d407f35004252005c940088500270900221000441800882001102002200, 0xe58320011568022a900450a008a04017350022650044c200f9340112480023d0044720088500110800220c00441000881001101002200, 0x6064002202, 0x300d006018002202, 0x180a8030131ce01e002202, 0x39e0807380a00301200601c000206, 0x180e8030191d0026002202, 0x3a20a87400d00301800601c002a06, 0x18138030211d2032002202, 0x7481100302000601c002206, 0x181980302b1d3042002202, 0x74c1600302a00601c002206, 0x22b5004562008aa4011468022890044da0089a407131002a550044a20008f80111e80003c0044740088500110800220c00441000881801102002200, 0x8ad401156803aa9006d0a00ca040713500226501c4c40a5985d4030002a4d004c920008f40011d0002390000700008500010800020c00041000081001101000200, 0x22bd004572008ac40114a8022910044ea0089c401731003e560044aa0001500112900024e0044940088500110800220c00441400882001102002200, 0x457a008ab401f54802285053504012a05d5040002e6a0164ca01098402b29002a4d00549400f92400024002a3d05047200a85001508002a0c00541000a81001101002a00, 0x11628022c1004572008a740114c8022760044ea0001d001139002a6e0044d40009980113100aa56005c940088500110800220e00441800882001102002200, 0x22c500455a008aa401142802281005cd4008994011310022610000c002c9340212480223d0014720088500110800220c00441000881002701002200, 0x8b34011648022c100453c008a740004e00229a00452c008a480394700228a00050c008a0814f3500b26600fc940088500110900221000441800882001102002200, 0x11668022ad00455200ca280114280228200450200020003f350022650044c20089340252480363d0064720088500110800220c00441000881002901002200, 0x606600c0c40181780302d006056002202, 0x605400c0800180c00301200601c002206],
  [0x4209f0801360e025c1b04982a08f05011606021c0b0418340770640e60981bc120358140670240c608815c1002981004f01c0960301280501f80803b0900261180482200880001007c01e0f00381d00680000c0600160b80281600480000803c00e0700180d00280000400c00601000801000800000, 0x1678002cb00158e007b0c0095f8016bb00055e0602b4001558160a900153e006a6c0094b800e9300050e050214001418120810014ee0019cc001338100650014c61281880703080c06000049e0281340032580804900046e0080d80101a8000340004660080c80101880003000042e1480580010a8020140004261400480010880201000041e1380380050680200c0004161300280030480200800040601800800100802000, 0x9009f11c13621825c4204987c08f0f41161a021c330418820771000e61e01bc3b0358640670c40c61d015c3902a8700530c009e17812c2e01f85a03b12c0262500484900880401011801e2280384400680400c00c0160000283f0048040080dc00e1b0018350028040040b00061580082a000804000, 0x11678022cb00458e328314011618c80c100457e008aec0115b803eb300455e2c82b401d558b00a900453e3182740114d8c409900452e008a4c01147804a8b006d0e2b8214019418ac0810044ee3001d86103a8be0740044e62f01c801f378b806e007cd62d81a8011338a80661540ca00898c520310a6061008cae01094c011278a204d005c962781285002489c04800547e2680f40131d89803900442e3380580110a80601400a4263300480110880601000041e0080380110680600c009c162e80280110480600800440e2d001801f028060040044061f800800100806000, 0x1e819e016b2c013638026c3004d7e3b82f40135d8ec0b9004d6e009acc700588026af00c556009a7c02f4d805e971d412a009a4c74048805e8f00bd1637822402f43805a83004cee3981d4013398e4071004cde0099ac013338006631b00c43681846b0300026570340ac0201540002a0026530100a400193c0102700804d00009800992c0402500563f1a407c3500f46801e00263b00ac2e3d80580130a808014004c263c804802f08808010004c1e3c00380130680800c004c1638802801304808008000c0e37001801302808004004c0626000800300808000, 0x1678002cb00558e00ab0c0155f802abb00056e01bacc015579100ad0055564302a88705490a0a800553e01da6c0394b80669300051e01aa2c0154390808500cd06410208830409020800054ee00a9cc01537802e6b2240d400a99c80032802a631f80c43f81847d030002a5700aca63481486a0288d005000549e0281340152580a04a0340920001200151f80a03d0004760280e80101c80003800542e4680580150a80a0140054264600480330880a01000541e4580380150680a00c00e4164500280150480a00800540e2680180010280a0040054063e00080150080a000, 0x53027ca504d9420972801264d823c9a0459240872441064f81dc9e03993206f2600d648019c8f03192e0572580a612813c0602691c04b0180944480fc6c01d8d60392a4026540048a700880c01029001e518038a200680c00c2740164e00288e00480c00825400e4a00189300280c00413c0062700082500080c000, 0x1780cf01159600bb1cba062802ec32e418200bafcb505e802ebb2d017200badc01759800aaf00155601fa7cb804e802e9b2dc13201fa5cb304a8086932c812200ba3c03f45807a8700f50600b9dc1603b00e0750000e800b9cc0703911c0710180e000b9bcb0037002e6b1c80d400299c0103300e0650000c800b98c07031002e572bc0ac00b94cae029002e4f2ac09c560134aa026002e4b23809400b8fc0031d8da039005c2e5e80580170a80e014005c265d804803f0880e010005c1e5b00380170680e00c0104165880280170480e008005c0e5680180170280e004005c062800080050080e000, 0x8b3c011658022c7004586008afc01f5d8022b7007566008abcc30568022ab308152008a7c0114d80229700952600da3c0194580228730410a008a0cc00408046770084e60089bc0173595606a2b00d25501a0011338100650044c6040188160308000600054ae00994c0112790004d007c965f81240111f81003d0004760400e80101c80003800442e6380580110a81001400a42663004801108810010008c1e6280380110681000c00441662002801f0481000800440e288018001028100040044065f000801100810000, 0x659e6a8338d60669a80cc006596698324019638032c334418200cafc0195d8032b7002d6600cabc0015580329f07413c0482740004e00329b02413400ca5ccf04b0032932dc124024a3ccd04700328b1d0114000a1c0104301208500010800ca0c090410032770064e600c9bc0493599806a011cce648198ca0329900640064c602695c04b2980324f00f4964781280351f805a3b00642e6b80580190a8120140144266900480190881201000041e6800380190681200c013c166700280190481200800640e658018049028120040064062b000800100812000, 0xdb3ce60668036cb006d8e00db0c01b5f8016bb00056e00eacc01b579c40ad006d567002a8e10549be0a8006d3e00da6c01b4b804a93006d1e023a2cc904519408932011000da1c0a0428036830281040e82040004000aa77014ce600d9bc03d3592006a006cce60819401b319ba0623780c26e01800012b805e53006c9e420134025259b404a36c0926c812001b1f81403d0004760500e80101c80003801642e73805801b0a814014006c2672804801b08814010015c1e72003801b0681400c006c1671802802504814008006c0e2b801800102814004006c066c000801b00814000, 0x759e1103380b0668000cc00759605832801d639e60c63d018a79031001d619a60c200757e7782f801d5d9720ba01756e7682d801d598ec0b200055e0082b80b0568000ac0075560582a801d4f803a9b3c413400ea5c01d49803a8f01751676022805b439d20863a810a74021001d41803a770074e600e9bc00735803a670004c602d95c05f29803a4f0014964881280371f80623b018c2e7b005801d0a8160140004267a804801d0881601000741e78003801d0681600c01841677002801d0481600800740e75801805d028160040074062c000800100816000, 0x8b3d040670022cb00458e008b0c0115f803ebb00456e02dacce90591d40b13a0160008abc0c0568022ab0301541102a40005400229f004536008a5c0074980028f006516008a1ce20428022833fc104800204fe0400046770084e60089bc0053592406a0044ce618194011319f80623f40c27d81800012b80265300449e44013401f259f204a3e80927c01200111f81803d0004760600e80101c80003800442e8280580110a81801400a42681804801108818010009c1e8100380110681800c00441680802801f0481800800440e2c8018001028180040044067b800801100818000, 0x2100cf00b59600fb1c01f61803eb705416a00facc14058803eaf01755600fa7c03b4d80728f04c11a012a2c12044804a8701250600f9bc11036803e6b0400d200f99c01731926062007c8e0681180d022800044007c860681080d02080004000547e0280f80131d80803a00542e84805801f0a81a014007c268380480250881a010007c1e83003801f0681a00c007c0e07801801f0281a004007c061500080030081a000, 0x23c09f4741368c825d18049a2808f44c11680821ceb041a2e0774580e68901bd110359c606732c0c688015d0f029a1604f4280966200fcad01d92803a4840269000491f00881c01047001e8d80391a00681c00c03c0160000291500481c00843800e8680190c00281c0041680061580082600081c000, 0x8b3c011658022c74c818a008b0d310608022bf004576008add2b05a803eb34a8162008abc01d5580229f4c013a008a6d2f04c802297004526008a3d29046804a8b4a011200da1c019418022774b80ec0089cd2d03900226f1500dc9381b4011358a406a4980d200099d230330072634880c401195d2502a8042534900a200893c0172592a04a00e47e4500f80031d8dc03a00442e9a00580110a81e01400a4269980480110881e010007c1e0680380110681e00c009c169600280110481e00800440e8a801801f0281e0040044061600080010081e000, 0x859e010b2c02163a7c0c50085869e83040215f8042bb00856e00facc0215780beab00853e9e02740214da7609900852e010a4c02147804a8b014d0e025a0c0213b82c0760400ea0001d002139820072007cde0681b81003680006c0084d60801a801533a6a0660084c639018801f2ba6e0564e00aa9b01500212980424f005c965701280151f80263b00842ea000580210a820014019c269f80480210882001001941e9d00380210682000c007c169c80280210482000800840e92001801f0282000400840616800800300820000, 0x8d9e011b2c02363a9e0c5008d8600fafc01f5d8046b7016d66011abd4c0568046ab528154a582a54905400469f53813a011a6c0394b804a9301551e026a2c02343a90085008d06a3020947040a8a080008cee00f9cd370392700714d80e00119bc0173595e06a008cce088194023318220620580c20001800152b802653008c9e08813401f2582204a0340920001200231f90003d001476a180e94401ca8403801542ea880580230a822014008c26a8004802308822010008c1ea680380230682200c008c1692802801f04822008008c0e17001800502822004008c06a0800802300822000, 0x767ac00cd001d96af832400763aba0c5001d86012afc06b5d80d2b7558166003abc00755804a9f07413c0902740004e004a9b048134012a5d5a04b2b6095564128012a4d3b049004a8f03411c09023400046004a8b048114003a1d52043005e831d01040129dc02539ab00720094deaa01b955036aa606c0094d601299c049319980620094ae01294c02527807e4b2600940198fc02f1d8de03a00942eb080580070a824014009426af00480250882401000cc1eae00380250682400c009416ab80280250482400800940e9400180250282400400940618800800700824000, 0x459e008b2c011638022c300457e01caec0115bacc0b5004566b282c401157803aab00453e008a6c0114b804a93550124aa82455304800228f04c11a008a2c1304503a08900011000da1c019418072770084e60089bd4803680226b5900d200899c017319320620044ae098154039298260520340a200014003927805e4b00447e4200f80091dac403a00442eb480580110a826014006c26b4004801108826010009c1eb380380110682600c0044169480280390482600800440eb180180110282600400440619000800900826000, 0x1f678440ce05019a00033001f658280ca002d8eba831800b61abe0c2007d7eb882f97205eae00bc007d769e82e801f5b81a0b605016a0002d001f598280b2002d5eb502b8013558ec0aa002d3eba027800b4d803e97007d26b7824801f47ad808e5b411ab5823001f45803e8701750676020801f3b80767300e4deab01ac00b33801663007cae00f94c01f27802e4b26809400a8fc0131d8e003a007c2ebb805801f0a828014005426bb004801f08828010007c1eb9803800b0682800c007c16b7002801f04828008007c0e95001801f02828004007c0619800800b00828000, 0x459e008b2c011638022c300457e00faed6c05d2da0b95ac170008adc1505a8022b30541641102c4000580022af007556008a7c0114d80229701a526008a3d6604680228b5ec11200da1c01941803e770084e60089bd4c03680226b5e80d200899c017319360620044ae0a815401f2982a0520340a20001400152780264b00447e4400f80091daf003a00442ebf00580110a82a01400a426be80480110882a010009c1ebe00380110682a00c00441695802801f0482a00800440ebc80180110282a0040044061a00080090082a000, 0x459e008b2c0115f8380bd0045760d82e40115b803eb300455e00eaac0114b8340950045260c824401147804a8b006d0e00ca0c0112f82c05e0580ba0001700112d82c05a0580b20001600232b8220560084a60801480112781004e005c960381280151f80263b00442ec000580110a82c01400a426bf80480110882c010009c160c00280110482c00800440e86001801f0282c0040044061a80080050082c000, 0x31e09f638136c5025d89049af808f5b811681021cee041b1007761c0e6b381bd570359c80673380c6c2815d84029b0604f608096c081288b01f8f003b648026c880499000882e01063401ec600398b00682e00c0600160000298600482e0084b000e8680190600282e0041740061b00082700082e000, 0x2767804ecb009d8ed0031402761b3e0c1009d7ece02f40275db360b9009d6e00facc0275780c2ab009d3ecf02740274db3a099009d2ecd025402749b32091009d1e012a2c05743809e83009ceecc01d85403a804e7365c0e42901c402337a9a06e007cd69c81a80233398a0660104c658818801f2bb2c056008ca6ca814800127b2804e008c96c981280151f80263b009c2ed100580270a83001401b426d0804802708830010009c1ec300380270683000c009c160b002802704830008009c0e87001801f02830004009c061b800800100830000, 0x22cf6ac19a008b2daa0648022c7004586008afc0115d8022b700ed66008abc01d5580229f07413c0c82740004e00229b064134008a5c1604b032095000128008a4c1904900768f69011c010a2d3b04500368768c10c00ca0cb70410022776980ecd381d5a503a0022730044de0129ad580350036670064c601195c0212980224f010c9659012803b1f805e3b00442ed600580110a832014004426d480480110883201000a41ed400380110683200c009c16ce80280110483200800440e88801803b028320040044061d800800d00832000, 0x22cf004596008b1c011618022bf6c417a008aedb005c8022b7007d66008abc01d5580229f004536d30269a704cb4a09800452e0d02540114983409207412200024001147804a8b006d0e00ca0c0113b8340750044e60d01c816038800070008cdea701b80213580226700fcc65981880112ba90056007ca6d701480112798204e001496d681280151f80263b00442ed980580110a83401400a426d9004801108834010009c1ecf00380110683400c01b416d780280110483400800440e89001801f028340040044061e000800500834000, 0x22cf08819c0d8334000660022cb06c194008b1dba0630022c36a8184008afc1605f0360bd000178008aec1b05d003eb76d416c010acd3d0590022af6d015c037aacb905500229f004536008a5db704b3700956d8128008a4c01147803e8b5bc114008a1c01d418022770044e60089bc06b358036670064c601195c0212980224f005c965a01280151f80263b009c2ede00580110a836014004426dd80480110883601000a41edc80380110683600c009c16cf80280110483600800440e89801801f028360040044061e800800f00836000, 0x22cf004596008b1c01161b6e0c26e0182db03000115f8380bd0045760e02e82205c8000b800456e00facc01157803aab00453e008a6c0114bb62095004526e0024401147804a8b006d0e00ca0c0113b8380750044e60e01c816038800070008cdea781b802135802267005cc65a81880112ba98056007ca6df01480112798604e001496de81280151f80263b00442ee100580110a83801400a426e0804801108838010009c1ed000380110683800c004416df80280110483800800440e8a001801f028380040044061f000800500838000, 0x22c708418a008b0c200608022bf004576008adc00b598022af0075560089fc1d03f03a07d0000f80089ec1d03d03a0790000f00089dc1a03b0022730640e40089bc13037004a6b0480d400d99c0a0330032630240c401195c0212980224f00fc965101280331f805e3b00442ee180580110a83a01400a41e0f80380110683a00c009c16c580280110483a00800440e8d00180250283a0040044062200080010083a000, 0x38209f6e4136be825d73049a0608f3c0116e6021dcb041aa00774fc0e66301bcbb03594606a7280cee4818c8c02b8f205372009ee3812dc601fb8a03b73c026e70049cd00883c01068401ec600397f00683c00c4cc0168d80290700483c00819800e2280182800283c00407c006000009c400083c000, 0x14b3ddb0668052cb768192014b1c029618052bf007d76014adc01d598052af76415a014aadd805480529f6c813c014a6da804d0036975a012c019a4d5c04900368f39411c000a2cd004500528775c10c2a021402941bac0821481020119dc0673980526f005cd65201a802933baa06500a4c6ea01840152b802653007c9ee9813401b25ba404900047ee880f401b1dba003900a42eee00580290a83e01400a426e200480290883e01001b41ec680380290683e00c00a4168e002801f0483e00800a40e2300180010283e00400a4060e80080290083e000, 0x11678440ce08019a000330011658400ca00458e0e8318200628000c40045861003080115fbbe0be004576d502e80115bbbc0b6001d66af82c800157bba0ae0065566982a80114fbc209e78813af002700114d802297004526008a3c00b458022870075067882080113b8022730044de0039ac01b338032633440c401195c0212980224f0114965281280011f805a3b00a42ef200580110a840014004426f180480110884001000a41eed00380110684000c009c16c700280110484000800440e8e801802d0284000400440623800800100840000, 0x459e008b2de10653c40c9780190008b1c210628022c3084184110304000600022bf004576008adc00b59ae80b200455e8202b801d5580229f08413a008a6c2104d03a099000130008a5c0114980228f001d16ae822801b439cc0860065060089ddb103b0022737a00e40089bd660373ce06b7980d400899ce20330002637940c401195c0212980224f2f00965301280011f8f403b00442ef500580110a84201400a426ed80480110884201000441ef480380110684200c009c16c780280110484200800440e8f00190800284200400440624000800100842000, 0x22a708814c110294000520022a30881441102840005000229f08413c008a6c2004d00229707012c008a4c1b04900228f05411c00fa2c1404500228703010c00ea0c0b0410022770044e60089bc007358036670064c601195c0212980224f005c965381280151f80263b0044261200480110884401000a41ee680380110684400c009c16c800280110484400800440e8f801801f0284400400440624800800100844000, 0x36609f6b0136b4825d610499ce08f35c116f9821df2041aa20775000e66381bcbd03595006a7c40cef8018c8d02b8f60537bc09ef7012ded01fbd803b770026e70049c300884601068801ec880398000684600c4d00169000290900484600819c00e25001829002846004090006000009eb000846000, 0x8b3dea0670022cb78c194008b1dc20630022c36ec184008afd7e05f002abb5d8174008add0505b0002b33d4164008abdfd0570a80ad004556fe02a85205480229f004536008a5c0254980b28f006516008a1dfb0428022837e810202a9dc0213980226f005cd65481a801133bf20650044c6fc01840152b80565300549efb813401125bec04900047efa80f40111dbe803900442ef580580110a84801400a426e7804801108848010009c1ec900380110684800c0044169080280150484800800440e2580180010284800400440611000801100848000],
  [0x4209f0801360e025c1b04982a08f05011606021c0b0418340770640e60981bc120358140670240c608815c1002981004f01c0960301280501f80803b0900261180482200880001007c01e0f00381d00680000c0600160b80281600480000803c00e0700180d00280000400c00601000801000800000]]

def witT8 : List ℕ := [0x140305c290981e, 0x440a0001c06c26, 0x5c110001b06826, 0x340305c290981e, 0x500d0001c06c29, 0x500305c290981e, 0x280505c290981e, 0x440505c290981e, 0xc000341e06c1a, 0x2800044260681b, 0x2400044260701b, 0x3400050290701b, 0x28000341e06c1a, 0xc000501e0701a, 0x44000501e0701a, 0x2400044260681b, 0x18030341e06c1a, 0xc0005c2606c1a, 0x4000028260681c, 0xc00034210781a, 0xc000342506c1a, 0x2800044260701b, 0x5c0d0282607829, 0x4400028260681c, 0x5c140442607829, 0x40000282606c1c, 0x5c000282606c1c, 0x5c00044260701b, 0x2400050290701b, 0x2406050290701b, 0x5c0a0001c06826, 0x50000342906c1c, 0x34060502908821, 0x3406050290701b, 0x5c0a0342907826, 0x280005c260701a, 0x5c00028260681c, 0x28060341e06c1a, 0x280005c2606c1a, 0x2800034210781a, 0x28000342506c1a, 0x18030501e0701a, 0xc0005c260701a, 0xc00050220781a, 0xc000502c0701a, 0x440005c2606c1a, 0x5c00044260681b, 0x44060501e0701a, 0x4400050220781a, 0x44000502c0701a, 0x1803034210781a, 0x18030342506c1a, 0x40000342906c1c, 0x40060342906c1c, 0xc00034250841a, 0x44000341e06c1a, 0xc0005c290981e, 0x181e0681a, 0xc030281b0681a, 0x341b0681a, 0x28000001a0681a, 0x44000001a0681a, 0x18000001a0681a, 0xc00050290701b, 0xc000341e0681a, 0xc000141e06c1a, 0xc000241e06c1a, 0xc000141e0701a, 0x28000001b06c1b, 0x18060181e0681a, 0x280a0181e0781a, 0x44110181e0781a, 0x181e0781a, 0x181e06c1b, 0x281b0681a, 0x1e0681a, 0x280a0281b0681a, 0x44110281b06c1a, 0xc030181e0681a, 0x5c0d0282606829, 0x5c140442606829, 0xc030441c0681a, 0x44060341e06c1a, 0xc0005c2606c1e, 0xc0005c290981a, 0x3400050260701b, 0x34000341e0681a, 0x50000341e06c1a, 0x28000281e0681a, 0xc030341b06c1a, 0x34000001b06c1b, 0x34030341b0681a, 0x341b06c1a, 0x501c0681a, 0x14030341b0681a, 0x18060341b06c1a, 0x5000034290841c, 0x3400050290881b, 0xc000281e0681a, 0x28000241e06c1a, 0x3400044260681b, 0x181b0681a, 0x181c0681a, 0x280a0001c0701a, 0x280a0001b06c1a, 0x280a05c1c0701a, 0x280a05c1c06c1a, 0x280a0341e06c1a, 0x3406044260701b, 0x3406044260681b, 0xc000501e06c1a, 0x44110001b06c1a, 0x44110001c0701a, 0x441105c1b06c1a, 0x44110501e0701a, 0xc000341e0701a, 0x5006028260681c, 0x5c000342906c1c, 0x5c00050290701b, 0x18060001b06c1a, 0x18060001c0701a, 0x340a05c290981e, 0x501105c290981e, 0xc000401e0701a, 0x341e0781a, 0x40000341e0701c, 0xc030341e0681a, 0xc000341e06c1b, 0xc00050290701a, 0xc000501e0701b, 0x24000341e0681a, 0xc000341e06c1c, 0x28000501e0701a, 0x501e0781a, 0xc000501e0681a, 0x24000501e06c1b, 0xc030501e0681a, 0xc000342906c1a, 0x40000501e0681a, 0xc000342906c1c, 0x44110441c0681a, 0x4400034210781a, 0x2806044260681b, 0x2400050290681b, 0x18000001b06c1b, 0x28000141e06c1a, 0xc030181b06c1a, 0x18030141e06c1a, 0x281e0781a, 0xc030281e0681a, 0x2400050290881b, 0x4000034290681c, 0xc000441e0681a, 0x181c06c1b, 0x44000141e0701a, 0xc030181c0701a, 0x18030141e0701a, 0x441e0781a, 0xc030441e0681a, 0x4000034290841c, 0x180305c290981e, 0x240000c260681b, 0x340a05c2909825, 0x5c0a0342906826, 0x44000501e06c1a, 0x3400044260701b, 0xc00044260701b, 0x400000c260681c, 0x340305c290981a, 0x500305c290981a, 0x5c0000c260681c, 0x5c0000c260681b, 0x440a0181e0681a, 0x1e06c1b, 0x18060281b06c1a, 0x340a05c290981a, 0x501105c290981a, 0x441c0681a, 0x3400050290701a, 0x5000034290681c, 0x50000342906c1a, 0x3400050290681b, 0x2800040290701b, 0x340305c290681e, 0x500305c290681e, 0x5c0d00c1e06829, 0x440a0001c06c1a, 0x5c030001c06826, 0x5c0d028260781b, 0x5c030001b06826, 0x340d0341e0681a, 0x340005c290981e, 0x340005c290701b, 0x3400040290701b, 0x34000441e0701b, 0x340a044260781b, 0x50140501e0681a, 0x500005c290981e, 0x50000241e06c1a, 0x50000281e06c1c, 0x280a0281e0681a, 0x5c14044260781c, 0x44000241e06c1a, 0x44110441e0681a, 0x5c030342907826, 0x5c0d044260781b, 0x50060341b0681a, 0x2800044260701a, 0x44000282606c1a, 0xc030501c0701a, 0x340000c260681b, 0x5c0a0341e06c26, 0xc0305c1c0701a, 0x5c1c0681a, 0x180605c1c0701b, 0x5c1705c1c06c1b, 0xc0305c1c06c1a, 0x34000341e06c1b, 0x3400014290701b, 0x5c030501e0701a, 0xc0305c1b06c1a, 0x5c1b0681a, 0x5c000001b06c1b, 0x34000501e06c1b, 0x1400050290701b, 0x5c030341e06c1a, 0x24000441e0681b, 0x280a0341e0781a, 0x440a0341e0681a, 0x340a044290981e, 0x44110501e0781a, 0x50000501e0681a, 0x5011028290981e, 0xc000282606c1a, 0x5c0500c2607829, 0x5c030142906826, 0x18290681a, 0x140305c290681e, 0xc00034290781a, 0xc00044260701a, 0x28060001e06c1a, 0x44060001e0701a, 0x280a0441c0701a, 0x3400040290701a, 0x50000242906c1a, 0x2800040260701b, 0x340a0341e0681a, 0x5011028260781a, 0x50110281e06c1a, 0x5c0000c2606829, 0x5c0d00c260781b, 0xc000341e06c26, 0x140505c1c0701b, 0xc00014290781a, 0xc03018290a41a]

def S8 (s i : ℕ) : List ℕ := unpackW wdT8 9 ((levT8.getD s []).getD i 0)

def N8 (s : ℕ) : ℕ := (levT8.getD s []).length

def A8 (s i tag : ℕ) : ℕ := findAct 4096 ((actT8.getD s []).getD i 0) tag

def W8 (w : ℕ) : ℕ := witT8.getD w 0

def Z8 (s : ℕ) := barrier 26 S8 N8 A8 W8 idRot s

theorem enc_inputs8 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT8) = xsT8 := by decide +kernel

theorem enc_goal8 : encL fT8 rowsT8 = goal 26 := by decide +kernel

theorem mask8 : mask 26 = 2 ^ rowsT8.length - 1 := by decide +kernel

theorem proper_fail8 : ∀ zs ∈ xsT8.sublists, zs ≠ xsT8 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked8 : ∀ s ≤ 8, ∀ i < N8 s, Z8 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun8 (s : ℕ) (hs : s ≤ 8) (h : NatRun (mask 26) (goal 26) s xsT8) : False := by
  have hc : NatRun (mask 26) (goal 26) 8 xsT8 := extend_run h hs
  have p : xsT8.Perm (S8 8 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked8 8 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub8 : ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsT8 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT8
  · subst e; exact noRun8 s hs h
  · exact proper_fail8 zs (List.mem_sublists.2 hz) e (required h)

theorem low8 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT8 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT8 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 8 h
  have hr : NatRun (mask 26) (encL fT8 rowsT8) s' (ws.map fun a => encL a rowsT8) :=
    Run.map (fun a : BFn 5 => encL a rowsT8)
      (fun a => by rw [mask8]; exact encL_inv a rowsT8)
      (fun a b => encL_and a b rowsT8) (fun a b => encL_or a b rowsT8) hrun
  rw [enc_goal8] at hr
  refine no_sub8 s' (by omega) _ ?_ hr
  rw [← enc_inputs8]
  exact hsub.map _

def mono8 : List Gate := [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [6, 12]⟩]

theorem mono_ok8 : ∀ g ∈ mono8, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono8, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval8 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono8, 13⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve8 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeac8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono8, 13, mono_ok8, ?_, mono_eval8⟩
  by_contra hlt
  have hlen : mono8.length = 9 := rfl
  apply low8
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 8
    omega

def rowsT9 : List ℕ := [1, 1, 2, 2, 3, 3, 3, 4, 4, 8, 9, 9, 9, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 5, 17, 6, 10, 7, 11, 19, 5, 6, 10, 11, 13, 25, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT9 : List ℕ := [0x24cf3cc001c73, 0x4b91df00e007c, 0x9d3a65470e180, 0xf23f8a380fe00, 0xffe410bff0000]

abbrev fT9 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT9 : List ℕ := [0x1bef400ffff, 0x811c0000070, 0x40a244000000, 0x910450000000, 0xdc075c7f01ff, 0x200f080001c00, 0x24c4108000000, 0x24ce34c000000, 0x24cf3cc001c73, 0x2ddf7dc001c73, 0x42118a0000000, 0x4b11cf0000000, 0x4b801000e0000, 0x4b91df00e007c, 0x4f9bff40e007c, 0x62c59ab8f1e7f, 0x66dfbec001c73, 0x6fd5df80e007c, 0x6fdfffc0e1c7f, 0x903a00000e000, 0x9d20000700000, 0x9d3a65470e180, 0xb46e20ff1ff83, 0xbde4108700000, 0xbdfe75c70e180, 0xbdff7dc70fdf3, 0xd23b8a000e000, 0xdb30c33ffe38c, 0xdf3bef470e180, 0xdfbbff47ee1fc, 0xf224003800000, 0xf2358a3800000, 0xf23f8a380fe00, 0xf63fae780fe00, 0xf6e410b800000, 0xf6ff9ab80fe00, 0xf6ffbef80fe73, 0xfb3fcf380fe00, 0xfbbfdf38efe7c, 0xff3fef7f0ff80, 0xffe410bff0000, 0xffee34fff0000, 0xffef3cfff1c73, 0xfff455bff0000, 0xfff59abff0000, 0xfff5dfbff007c, 0xfffe75fffe180, 0xffff9abfffe00]

def levT9 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x290841603809, 0x290841c0580e, 0x290841705809, 0x290841003809, 0x290580e02405, 0x210580e02401, 0x290841c05c16, 0x290841c0400e, 0x290701603805, 0x210701603801, 0x290841604c02, 0x290841a03803, 0x210601603809, 0x290841603c09, 0x290881603809, 0x2a0841603809, 0x290941603806, 0x230841603809, 0x2b0841603807, 0x290841604809, 0x290841903809, 0x290901603809, 0x290841704009, 0x2905c1602405, 0x2105c1602401, 0x290841e02404, 0x2906c1603809, 0x29084160380a, 0x290981603809, 0x2c0841603809, 0x2909c1602c09, 0x29084160440e, 0x290841d03809, 0x2d0841603809, 0x2e0841603409, 0x290801603809, 0x290400e02405, 0x210400e02401, 0x290841603009, 0x290a01403809, 0x290841603808, 0x2f0841503809, 0x160380901401, 0x3007c1603809],
  [0x290841603809, 0xa4210580e02409, 0x290841c0580e, 0xa4210701603809, 0xa4210581303809, 0xa4210580e02402, 0xa4210681603809, 0xa4210580e02403, 0xa4250841603809, 0xa4210580e02406, 0xac290841603809, 0xa4210580e02407, 0xa4210580e03809, 0x290841705809, 0xa42105c1603809, 0xa4210781603809, 0xa4210580e02404, 0xa4270841603809, 0xa4210580e02c09, 0xb8290841603809, 0xa4210580e03409, 0xa4210581603809, 0x290841003809, 0xa4210581003809, 0xa4280841603809, 0xa4210581403809, 0xbc290841603809, 0xa4210581503809, 0xa4210841603809, 0x290580e02405, 0xa4210580e02405, 0xc0290841603809, 0xa42107c1603809, 0xa4290841603809, 0x210580e02401, 0xa4210580e02401],
  [0x290841603809]]

def actT9 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x610000c1800182000302000600, 0x60a, 0x60a, 0x60a, 0x602, 0x602, 0x0, 0x0, 0x0, 0x0, 0x16c9200e8f401d1d003a1000741800e82001d02003a00, 0x15a580614100be6200ac9a01592805d1d00561000ac1801582002b02005600, 0x4e20169340071c800e10001c1800382000702000e00, 0x32a140632480121000241800482000902001200, 0x661000cc1801982003302006600, 0x4a1402b2500121000241800482000902001200, 0xdd3c01b99403731006e1000dc1801b82003702006e00, 0x2699005ce40099b80131c802610004c1800982001302002600, 0x19d2c01da2803b4280768200ecc401d92803b1d00761000ec1801d82003b02007600, 0x610000c1800182000302000600, 0xa780014b004a8a0005040049340211c80021000041800082000102000200, 0x4d3c009a280131c802610004c1800982001302002600, 0x0, 0x0, 0x0, 0x1fa0803f3b007e6200fc9a01f92803f1d007e1000fc1801f82003f02007e00, 0xce20359540691d000610000c1800182000302000600, 0x99b404128802610004c1800982001302002600, 0x99b403f29002610004c1800982001302002600, 0x610000c1800182000302000600, 0x10d140219d80433680866a01b4c40219480431c808610010c1802182004302008600, 0x610000c1800182000302000600, 0x1a740033b00066a002cc40099540051d000610000c1800182000302000600, 0xd3a00598806f1d000610000c1800182000302000600, 0x1153a022a3404545008a1001141802282004502008a00, 0x69a006524004a1806f1d000610000c1800182000302000600, 0x0, 0x0, 0x4d3a009a280153b00266a002cc40099480131c802610004c1800982001302002600, 0x9a750134e40269b404d29009a1001341802682004d02009a00, 0x253c01ea58025450012820024c40049280091d00121000241800482000902001200, 0xa295014524039a140712500a2100144180288200510200a200, 0x0, 0x15d3a02ba680754900ae10015c1802b8200570200ae00],
  [0xd3e001a6c0034b803293000d1e001a2c00143801a83000cee00b9cc0033780066b000cce00598c0132b80225300249e00392c0031f800a3b006c2602804800308800010000c1e0200380030680000c000c1601802801504800008003c0e01001800302800004000c0600800800100800000, 0x55a006aa4003428016810024ca00398400326800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x480480100801000e00401800182c0000500200801c00c00801006001002000, 0x6c5000d82001a740034c802a760054e40019b800335000666000cc40018500030800020e000c1800182000302000600, 0x35e801ab9009562010ab40034a80529100151a005a040273a800671008cd20039840032b000a550000a800294800127000a4d00009800292801d1f003e3d02807800285000508000a0c000c1400282000502000a00, 0xd5a001aa400342800681000cca00a98401d29003e510280a0001934003250006490000900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1d8c000b140c0620006c100bd72001a740134c802a76001cea0001d00073900266e000cd400099800732800064001cc401593802d2681604c001c720038500070800060e001c1800382000702000e00, 0x4ad4003568012aa0025520782a00034280128200cd0207020002b35005a6902c0d000499400931002a610000c0001934009250062490340900048f40091d0002390000700048500090800120c00241000481000301001200, 0xb670026cd044198014b2400b6080069e002d3a00027000b4d002a96004d24001a3802945000286002d0a00021000b41007272002cdc01a99803732820064002c7200585000309001610002c1800582000b02001600, 0xd5a001aa403545006e89040110001a14003410006810001000019940153080064d000c920018f40031d0002390000700018500030800060c000c1000181000301000600, 0x6ce00359a00033000d650006c600a58401eaf80035d0006b6003564000ab800d568000ac00355400ca480014300768504810800d85800d0a001a1000341800682000d02001a00, 0xb3800163004aba00056401dac4120580002ad000554001aa400054000685000504009a041504000126d000cca00098803d308280600084a20019340012500064904c0900008f40011d0002390000700008500010800020c00041000081000301000200, 0xd6a001ac400346800689004cda0089a40032300064500008800190800320800040000c7c0028e80030a000610000c1800781800302000600, 0xc00480200802e00e00801800782c0000500400805800c01001006001004000, 0x1ec5000d82001a7400f4c802a76004ce40019b800335000266004cc400785000f0800060e003c1800782000f02001e00, 0xd8a008b040114f00069d068138008a6401148802a760044ea0001d00113900066e0044da0001b001135001266000cc401f9580412a832054008c7400885001108001e0e00441800882001102002200, 0x1ab4013550006a9074150009a5400342802682004d020e020003f390082710640e000999401331002a610000c0009934013250006490000900018f40131d000a3906c0700098500130800260c004c1000981000301002600, 0x6cd000d92001a780034e80009c000d3400aa580114900068e000d1a0002300034500068600a50400b9c80033700866d0780d800185000f09000610000c1800182000302000600, 0x1b340035a8006b2000d621082c00034f000692010d220f02400034680068a000d1200022000b41002675000cda0019a801534840068000caa001948003288000500014940018f80011d00063907c0700018500030800060c000c1000181800302000600, 0x3670006cd000198001b28003630006c508c188001b0803d5f0022ba000d6c001ad40005a0006b200055c006aa80034d00929201151c023a3422046004a860094740018580030a000610000c1800182000302000600, 0x11574023ae42205c0006b5000d64001ac40005800068d000d120019b401534800655000ca40019440002800063e0004740018500030800060c000c1002581800302000600, 0xd7a00cae40034a802e910054bc00a9740002e002a5a0054b20001600132b00225200249c0039280150a002a10000c1400a82001502002a00, 0x1280480300804800e00c01800182c0000500600805800c01801007001006000, 0x6bd000d72001a5400348800675000ce20019580032900024e0004940018500030800060c00541400182000302000600, 0x366809ec9005d8a001a780174e80009c005d3400aa580174a800094005d24009a380174684c08c004514000a1801341002a760134ea1381d0017350072620044a400b85000309002e10005c1800b82001702002e00, 0x6bd000d7200aa6804d4c84e098000d2a001a4800348800090000d1c0019d400339002a710000e00019580032900064e0004940018500030800060c000c1400182000302000600, 0x3670032cd00019800cb2800363009ec200557c00caf40005e0032ba000d6c008ac8009570032ad0a0158001aa80194f007a9601452a1482500494500328200bc940018580190a00321000641800c82001902003200, 0x7ac20145821483000035e8006ba000d720002e000157000695000d220019d400339002a710000e00019580032900064e0004940018500030800060c000c1400182000302000600, 0xd8a001b040033f00067d0000f80019e80033c800078000cec00b9c80033700066a000ccc0059880030a00060e000c1800182000302000600, 0x1500480400804800e0100180b80280400401000601000800180c00001008000, 0x6ad000d52001a140034080aa65000cc20019340032480a63d000c720018500030800060c000c1000181000301000600, 0x3670006cd000198001b28003630006c5000188001b080035f009eba000d6c001ac8001570052aa015d3c02ca742b04e00068a002cc400d8580030a000610000c1800182000302000600, 0x15d9402cb242b0640006c5000d84001b04000600032ba00055c001a740034d00069900013000ba48003470006760054e40019b8003350006660004c40018500030800060e000c1800182000302000600, 0xd4c001a94000520006a2000d420002800034f00069a000d2c00ca480034700068a00050c006a0801b09000610000c1800182000302000600, 0x1500480500804a00e0140180c00280500401200601400800d80c0000100a000, 0x6ad000d52001a1401b40802a650054c200d9340032480023d00047200d85001b0800360c006c1000d81000301003600],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT9 : List ℕ := [0x1c020281d0681c, 0x1c000441c06c1a, 0x5c0d0001b06829, 0x5000034290681b, 0x1c0205c290741c, 0x340005c2906c1a, 0x50000441c06c1a, 0x1c00044200701a, 0x1c040441c06c1a, 0x1c0005c2906c1a, 0x4000034290681b, 0x280705c2906c1a, 0x440705c290741c, 0x1c000442c06c1a, 0x281d0681a, 0x441b0681a, 0x5c140081d06829, 0x3402050290701d, 0x500205c290741c, 0x500d0101d06c29, 0x34000441c06c1a, 0x101c0681a, 0x1c070501b0681a, 0x1c040281d0681c, 0x5c140081d07029, 0x340a0441c06c1a, 0x101d0681a, 0x34000001a0681a, 0x340a05c2906c1a, 0x50000001a0681a, 0x2402050290701d, 0x10000001a0681a, 0x1c040341d0681a, 0x1c000341c0681a, 0x1c000081c06c1a, 0x1c000401c06c1a, 0x501105c290741c, 0x1c000442c0801a, 0x28000001a0681a, 0x28070441c06c1a, 0x1c000441c0681a, 0x1c02028250741c, 0x4000034290941b, 0x281b0681a, 0x1c000441d0681a, 0x10040281d0741a, 0x10040101c0681a, 0x280a0101c0701a, 0x50140101c0701a, 0x1c040501b0681a, 0x1c0205c290741a, 0x50140001b06c1a, 0x3400050290701d, 0x1c000341d0681a, 0x34000341c0681a, 0x1c0005c290741c, 0x441c0701a, 0x1c070441c0681a, 0x28070281b0681a]

def S9 (s i : ℕ) : List ℕ := unpackW wdT9 9 ((levT9.getD s []).getD i 0)

def N9 (s : ℕ) : ℕ := (levT9.getD s []).length

def A9 (s i tag : ℕ) : ℕ := findAct 4096 ((actT9.getD s []).getD i 0) tag

def W9 (w : ℕ) : ℕ := witT9.getD w 0

def Z9 (s : ℕ) := barrier 26 S9 N9 A9 W9 idRot s

theorem enc_inputs9 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT9) = xsT9 := by decide +kernel

theorem enc_goal9 : encL fT9 rowsT9 = goal 26 := by decide +kernel

theorem mask9 : mask 26 = 2 ^ rowsT9.length - 1 := by decide +kernel

theorem proper_fail9 : ∀ zs ∈ xsT9.sublists, zs ≠ xsT9 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked9 : ∀ s ≤ 7, ∀ i < N9 s, Z9 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun9 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 26) (goal 26) s xsT9) : False := by
  have hc : NatRun (mask 26) (goal 26) 7 xsT9 := extend_run h hs
  have p : xsT9.Perm (S9 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked9 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub9 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT9 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT9
  · subst e; exact noRun9 s hs h
  · exact proper_fail9 zs (List.mem_sublists.2 hz) e (required h)

theorem low9 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT9 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT9 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 26) (encL fT9 rowsT9) s' (ws.map fun a => encL a rowsT9) :=
    Run.map (fun a : BFn 5 => encL a rowsT9)
      (fun a => by rw [mask9]; exact encL_inv a rowsT9)
      (fun a b => encL_and a b rowsT9) (fun a b => encL_or a b rowsT9) hrun
  rw [enc_goal9] at hr
  refine no_sub9 s' (by omega) _ ?_ hr
  rw [← enc_inputs9]
  exact hsub.map _

def mono9 : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [9, 11]⟩]

theorem mono_ok9 : ∀ g ∈ mono9, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono9, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval9 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono9, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve9 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaece0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono9, 12, mono_ok9, ?_, mono_eval9⟩
  by_contra hlt
  have hlen : mono9.length = 8 := rfl
  apply low9
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

end PEqualNP.Outside.L_meta_1441

theorem PEqualNP.Outside.L_meta_1441 : ∀ T ∈ ({0xfeeaeac0, 0xeeeaeaaa, 0xeeeaeae8, 0xeeeaece8, 0xeeeaeee0, 0xfee8eae8, 0xfee8eee0, 0xfeeaeaa8, 0xfeeaeac8, 0xfeeaece0} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hops _ heval
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1441.solve0 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve1 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve2 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve3 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve4 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve5 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve6 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve7 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve8 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1441.solve9 gates o hops heval
