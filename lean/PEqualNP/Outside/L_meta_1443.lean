import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1443

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

def rowsT0 : List ℕ := [1, 2, 2, 3, 3, 3, 4, 4, 5, 5, 5, 8, 8, 9, 9, 9, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 17, 6, 10, 7, 11, 19, 6, 12, 7, 13, 21, 10, 12, 11, 13, 25, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT0 : List ℕ := [0x24f9ce400e739, 0x4b8a5f80e003e, 0x9d15f287007c0, 0xf23ea5380f800, 0xffe1087ff0000]

abbrev fT0 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT0 : List ℕ := [0x24e1084000000, 0x24f9ce400e739, 0x4b8a5f80e003e, 0x9d15f287007c0, 0xf23ea5380f800, 0xffe1087ff0000]

def levT0 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x140400c01],
  [0x60140400c02]]

def actT0 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x9880012500023a00041800082000102000200],
  [0x50c000a140004200021000041800082000102000200]]

def witT0 : List ℕ := [0x180102c210701b]

def S0 (s i : ℕ) : List ℕ := unpackW wdT0 9 ((levT0.getD s []).getD i 0)

def N0 (s : ℕ) : ℕ := (levT0.getD s []).length

def A0 (s i tag : ℕ) : ℕ := findAct 4096 ((actT0.getD s []).getD i 0) tag

def W0 (w : ℕ) : ℕ := witT0.getD w 0

def Z0 (s : ℕ) := barrier 26 S0 N0 A0 W0 idRot s

theorem enc_inputs0 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT0) = xsT0 := by decide +kernel

theorem enc_goal0 : encL fT0 rowsT0 = goal 26 := by decide +kernel

theorem mask0 : mask 26 = 2 ^ rowsT0.length - 1 := by decide +kernel

theorem proper_fail0 : ∀ zs ∈ xsT0.sublists, zs ≠ xsT0 → (cov 26 zs &&& lo 26) ≠ lo 26 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked0 : ∀ s ≤ 5, ∀ i < N0 s, Z0 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun0 (s : ℕ) (hs : s ≤ 5) (h : NatRun (mask 26) (goal 26) s xsT0) : False := by
  have hc : NatRun (mask 26) (goal 26) 5 xsT0 := extend_run h hs
  have p : xsT0.Perm (S0 5 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked0 5 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub0 : ∀ s ≤ 5, ∀ zs : List ℕ, zs.Sublist xsT0 → NatRun (mask 26) (goal 26) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT0
  · subst e; exact noRun0 s hs h
  · exact proper_fail0 zs (List.mem_sublists.2 hz) e (required h)

theorem low0 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT0 5 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT0 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 5 h
  have hr : NatRun (mask 26) (encL fT0 rowsT0) s' (ws.map fun a => encL a rowsT0) :=
    Run.map (fun a : BFn 5 => encL a rowsT0)
      (fun a => by rw [mask0]; exact encL_inv a rowsT0)
      (fun a b => encL_and a b rowsT0) (fun a b => encL_or a b rowsT0) hrun
  rw [enc_goal0] at hr
  refine no_sub0 s' (by omega) _ ?_ hr
  rw [← enc_inputs0]
  exact hsub.map _

def mono0 : List Gate := [⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [6, 9]⟩]

theorem mono_ok0 : ∀ g ∈ mono0, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono0, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval0 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono0, 10⟩ (List.ofFn x) =
    Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve0 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono0, 10, mono_ok0, ?_, mono_eval0⟩
  by_contra hlt
  have hlen : mono0.length = 6 := rfl
  apply low0
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 5
    omega

def rowsT1 : List ℕ := [0, 2, 2, 4, 4, 8, 10, 10, 10, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 1, 3, 6, 5, 6, 9, 11, 14, 26, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT1 : List ℕ := [0x1534d600000, 0x2aebac071c6, 0x334d3998618, 0x3c8fc1e07e0, 0x3ff201ff800]

abbrev fT1 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT1 : List ℕ := [0x1534d600000, 0x2acb2800000, 0x2aebac071c6, 0x334d3998618, 0x3c8201e0000, 0x3c8fc1e07e0, 0x3fcf39f8618, 0x3ff201ff800]

def levT1 : List (List ℕ) :=
  [[0x801],
  [0x700c01],
  [0x140400c01],
  [0x80180400c01]]

def actT1 : List (List ℕ) :=
  [[],
  [0x54],
  [0x70],
  [0x9c]]

def witT1 : List ℕ := []

def S1 (s i : ℕ) : List ℕ := unpackW wdT1 9 ((levT1.getD s []).getD i 0)

def N1 (s : ℕ) : ℕ := (levT1.getD s []).length

def A1 (s i tag : ℕ) : ℕ := findAct 4096 ((actT1.getD s []).getD i 0) tag

def W1 (w : ℕ) : ℕ := witT1.getD w 0

def Z1 (s : ℕ) := barrier 21 S1 N1 A1 W1 idRot s

theorem enc_inputs1 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT1) = xsT1 := by decide +kernel

theorem enc_goal1 : encL fT1 rowsT1 = goal 21 := by decide +kernel

theorem mask1 : mask 21 = 2 ^ rowsT1.length - 1 := by decide +kernel

theorem proper_fail1 : ∀ zs ∈ xsT1.sublists, zs ≠ xsT1 → (cov 21 zs &&& lo 21) ≠ lo 21 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked1 : ∀ s ≤ 3, ∀ i < N1 s, Z1 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun1 (s : ℕ) (hs : s ≤ 3) (h : NatRun (mask 21) (goal 21) s xsT1) : False := by
  have hc : NatRun (mask 21) (goal 21) 3 xsT1 := extend_run h hs
  have p : xsT1.Perm (S1 3 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked1 3 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub1 : ∀ s ≤ 3, ∀ zs : List ℕ, zs.Sublist xsT1 → NatRun (mask 21) (goal 21) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT1
  · subst e; exact noRun1 s hs h
  · exact proper_fail1 zs (List.mem_sublists.2 hz) e (required h)

theorem low1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT1 3 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT1 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 3 h
  have hr : NatRun (mask 21) (encL fT1 rowsT1) s' (ws.map fun a => encL a rowsT1) :=
    Run.map (fun a : BFn 5 => encL a rowsT1)
      (fun a => by rw [mask1]; exact encL_inv a rowsT1)
      (fun a b => encL_and a b rowsT1) (fun a b => encL_or a b rowsT1) hrun
  rw [enc_goal1] at hr
  refine no_sub1 s' (by omega) _ ?_ hr
  rw [← enc_inputs1]
  exact hsub.map _

def mono1 : List Gate := [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 7]⟩]

theorem mono_ok1 : ∀ g ∈ mono1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono1, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem mono_eval1 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono1, 8⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve1 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaeaea (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono1, 8, mono_ok1, ?_, mono_eval1⟩
  by_contra hlt
  have hlen : mono1.length = 4 := rfl
  apply low1
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 3
    omega

def rowsT2 : List ℕ := [1, 1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 12, 12, 16, 18, 18, 18, 20, 20, 24, 24, 28, 28, 3, 5, 9, 17, 3, 6, 10, 5, 6, 9, 10, 13, 14, 17, 19, 22, 26, 21, 22, 25, 26, 29, 30]

def xsT2 : List ℕ := [0x15354f80000f, 0x2aeab881c070, 0x334cd1661980, 0x3c8f22781e00, 0x3ff0047fe000]

abbrev fT2 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT2 : List ℕ := [0x15354f80000f, 0x2aeab881c070, 0x334cd1661980, 0x3c8f22781e00, 0x3fcff37e1f80, 0x3ff0047fe000]

def levT2 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x180500801],
  [0x60100300801]]

def actT2 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x9c80033500026600041800082000102000200],
  [0x534000a48003450002860004e40009c40003800021000041800082000102000200]]

def witT2 : List ℕ := [0x100001c1c06017, 0x1c000101c05c18]

def S2 (s i : ℕ) : List ℕ := unpackW wdT2 9 ((levT2.getD s []).getD i 0)

def N2 (s : ℕ) : ℕ := (levT2.getD s []).length

def A2 (s i tag : ℕ) : ℕ := findAct 4096 ((actT2.getD s []).getD i 0) tag

def W2 (w : ℕ) : ℕ := witT2.getD w 0

def Z2 (s : ℕ) := barrier 23 S2 N2 A2 W2 idRot s

theorem enc_inputs2 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT2) = xsT2 := by decide +kernel

theorem enc_goal2 : encL fT2 rowsT2 = goal 23 := by decide +kernel

theorem mask2 : mask 23 = 2 ^ rowsT2.length - 1 := by decide +kernel

theorem proper_fail2 : ∀ zs ∈ xsT2.sublists, zs ≠ xsT2 → (cov 23 zs &&& lo 23) ≠ lo 23 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked2 : ∀ s ≤ 5, ∀ i < N2 s, Z2 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun2 (s : ℕ) (hs : s ≤ 5) (h : NatRun (mask 23) (goal 23) s xsT2) : False := by
  have hc : NatRun (mask 23) (goal 23) 5 xsT2 := extend_run h hs
  have p : xsT2.Perm (S2 5 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked2 5 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub2 : ∀ s ≤ 5, ∀ zs : List ℕ, zs.Sublist xsT2 → NatRun (mask 23) (goal 23) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT2
  · subst e; exact noRun2 s hs h
  · exact proper_fail2 zs (List.mem_sublists.2 hz) e (required h)

theorem low2 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT2 5 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT2 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 5 h
  have hr : NatRun (mask 23) (encL fT2 rowsT2) s' (ws.map fun a => encL a rowsT2) :=
    Run.map (fun a : BFn 5 => encL a rowsT2)
      (fun a => by rw [mask2]; exact encL_inv a rowsT2)
      (fun a b => encL_and a b rowsT2) (fun a b => encL_or a b rowsT2) hrun
  rw [enc_goal2] at hr
  refine no_sub2 s' (by omega) _ ?_ hr
  rw [← enc_inputs2]
  exact hsub.map _

def mono2 : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [8, 9]⟩]

theorem mono_ok2 : ∀ g ∈ mono2, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono2, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval2 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono2, 10⟩ (List.ofFn x) =
    Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve2 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeaeee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono2, 10, mono_ok2, ?_, mono_eval2⟩
  by_contra hlt
  have hlen : mono2.length = 6 := rfl
  apply low2
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 5
    omega

def rowsT3 : List ℕ := [1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 8, 8, 12, 12, 16, 16, 20, 20, 24, 24, 28, 28, 5, 9, 17, 6, 10, 18, 7, 11, 19, 5, 6, 9, 10, 13, 14, 17, 18, 21, 22, 25, 26, 29, 30]

def xsT3 : List ℕ := [0x1555e38001c7, 0x2aaafc0001f8, 0x333324e66600, 0x3c3c49787800, 0x3fc0927f8000]

abbrev fT3 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT3 : List ℕ := [0x1555e38001c7, 0x2aaafc0001f8, 0x333324e66600, 0x3c3c49787800, 0x3f3f6dfe7e00, 0x3fc0927f8000, 0x3ff3b6ffe600, 0x3ffcdb7ff800, 0x3fffff8001ff, 0x3ffffffffe00]

def levT3 : List (List ℕ) :=
  [[0x2809],
  [0x901805, 0x901c04, 0x902003, 0xa00801],
  [0x240601003, 0x180500801, 0x1c0400801, 0x200300801],
  [0x60100300801]]

def actT3 : List (List ℕ) :=
  [[],
  [0x38, 0x38, 0x38, 0x38],
  [0x1014001024000038, 0x3038000038, 0x3038002038, 0x3038004038],
  [0xc13001024001038000038]]

def witT3 : List ℕ := []

def S3 (s i : ℕ) : List ℕ := unpackW wdT3 9 ((levT3.getD s []).getD i 0)

def N3 (s : ℕ) : ℕ := (levT3.getD s []).length

def A3 (s i tag : ℕ) : ℕ := findAct 4096 ((actT3.getD s []).getD i 0) tag

def W3 (w : ℕ) : ℕ := witT3.getD w 0

def Z3 (s : ℕ) := barrier 23 S3 N3 A3 W3 idRot s

theorem enc_inputs3 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT3) = xsT3 := by decide +kernel

theorem enc_goal3 : encL fT3 rowsT3 = goal 23 := by decide +kernel

theorem mask3 : mask 23 = 2 ^ rowsT3.length - 1 := by decide +kernel

theorem proper_fail3 : ∀ zs ∈ xsT3.sublists, zs ≠ xsT3 → (cov 23 zs &&& lo 23) ≠ lo 23 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked3 : ∀ s ≤ 3, ∀ i < N3 s, Z3 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun3 (s : ℕ) (hs : s ≤ 3) (h : NatRun (mask 23) (goal 23) s xsT3) : False := by
  have hc : NatRun (mask 23) (goal 23) 3 xsT3 := extend_run h hs
  have p : xsT3.Perm (S3 3 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked3 3 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub3 : ∀ s ≤ 3, ∀ zs : List ℕ, zs.Sublist xsT3 → NatRun (mask 23) (goal 23) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT3
  · subst e; exact noRun3 s hs h
  · exact proper_fail3 zs (List.mem_sublists.2 hz) e (required h)

theorem low3 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT3 3 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT3 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 3 h
  have hr : NatRun (mask 23) (encL fT3 rowsT3) s' (ws.map fun a => encL a rowsT3) :=
    Run.map (fun a : BFn 5 => encL a rowsT3)
      (fun a => by rw [mask3]; exact encL_inv a rowsT3)
      (fun a b => encL_and a b rowsT3) (fun a b => encL_or a b rowsT3) hrun
  rw [enc_goal3] at hr
  refine no_sub3 s' (by omega) _ ?_ hr
  rw [← enc_inputs3]
  exact hsub.map _

def mono3 : List Gate := [⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [6, 7]⟩]

theorem mono_ok3 : ∀ g ∈ mono3, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono3, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

theorem mono_eval3 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono3, 8⟩ (List.ofFn x) =
    Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve3 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xeeeeeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono3, 8, mono_ok3, ?_, mono_eval3⟩
  by_contra hlt
  have hlen : mono3.length = 4 := rfl
  apply low3
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 3
    omega

def rowsT4 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 8, 12, 12, 12, 17, 17, 17, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 5, 9, 3, 6, 10, 5, 6, 9, 10, 13, 14, 28, 19, 21, 25, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT4 : List ℕ := [0x93ca9e00e007, 0x12e5572070038, 0x274b9a4381cc0, 0x3c93e49c01f00, 0x3ffe001ffe000]

abbrev fT4 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT4 : List ℕ := [0xa8c001fc7, 0x1560001ff8, 0x19a4001cc0, 0x1e48001f00, 0x1ffe001fff, 0x24012000000, 0x108884000000, 0x241120000000, 0x36c1b63fe0ff, 0x36dffe3fffff, 0x810a08000000, 0x93c00000e000, 0x93ca9e00e007, 0x93dffe00ffff, 0xb7dbbe00e007, 0x1081440000000, 0x12e4000070000, 0x12e5572070038, 0x12e5ffe071fff, 0x13eddf6070038, 0x18b465bc7e33f, 0x18b5fffc7ffff, 0x19bdede00e007, 0x1af5f7a070038, 0x1bfdffe07e03f, 0x2402000000000, 0x2403800001c00, 0x274a000380000, 0x274a1a43800c0, 0x274a884380000, 0x274b120380000, 0x274b9a4380000, 0x274b9a4381cc0, 0x276f9b6381cc0, 0x2d1a001f8e000, 0x2d1aa8df8ffc7, 0x2d3ea9e00e007, 0x2f5bbac381cc0, 0x2f7e00038e000, 0x2f7ea9e38e007, 0x2f7fbbe38fcc7, 0x36c2001ff0000, 0x36c3561ff1ff8, 0x36e7572070038, 0x37cbde4381cc0, 0x37ee0003f0000, 0x37ef5723f0038, 0x37efdf63f1cf8, 0x3c92001c00000, 0x3c92649c00300, 0x3c92a09c00000, 0x3c93441c00000, 0x3c93e49c00000, 0x3c93e49c01f00, 0x3cb7e5bc01f00, 0x3d9becdc01f00, 0x3dbe001c0e000, 0x3dbea9fc0e007, 0x3dbfedfc0ff07, 0x3ed3f69c01f00, 0x3ef6001c70000, 0x3ef7573c70038, 0x3ef7f7bc71f38, 0x3fda001f80000, 0x3fdbfedf81fc0, 0x3ffe001ffe000, 0x3ffe013ffe000, 0x3ffe1b7ffe0ff, 0x3ffe65bffe33f, 0x3ffe885ffe000, 0x3ffea09ffe000, 0x3ffea9fffe007, 0x3fff121ffe000, 0x3fff441ffe000, 0x3fff573ffe038, 0x3fff9a5fffcc0, 0x3fffe49ffff00, 0x3ffffffffe03f]

def levT4 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x4109412, 0x410b00d],
  [0x1083608819, 0x1083708419, 0xd8200480d, 0xd4210480d, 0x108360a414, 0x1083b08418, 0x108360c00f, 0x1083f08417, 0xc8150480d, 0xc8210480d, 0x1041a0480d, 0xd82508412, 0xd82c0840d, 0x741203409, 0xd81d0480d],
  [0x420d8210480d, 0x420d82b08412, 0x480d8210480d, 0x420d8240840d, 0x4b0d8210480d, 0x420d8150480d, 0x360841c0480d, 0x420841203409, 0x360c4210480d, 0x360841203405, 0x420d82b09021, 0x4b0d82b08412, 0x420d82b05412, 0x360ac2107012, 0x360ac2a08412, 0x420ac2104809, 0x360c42b08412, 0x360ac2104805, 0x480d82b08412, 0x360a8210480d, 0x420d82106406, 0x4e0d8210480d, 0xd821070190480d, 0xd831084190480d, 0x420d8220480d, 0x420dc210480d, 0x430d8210480d, 0x420d82904807, 0x108410d8290480d, 0x3609c210480d, 0x420d8210500d, 0x420e0210480d, 0x460d8210480d, 0x420ec210480b, 0x108410ec210480d, 0x390d8210480d, 0x420d8210600d, 0x420d8260480d, 0x470d8210480d, 0x480d8240840d, 0x480d8150480d, 0x360841e0480d, 0x480841203409, 0x360cc210480d, 0x360841203402, 0x480d8210480c, 0x420d8240540d, 0x36090210700d, 0x36090230840d, 0x420902103409, 0x360c4240840d, 0x360902103405, 0x4b0d8240840d, 0x3608c210480d, 0x420d83003408, 0x108410d8300480d, 0x360b8210480d, 0x420d8210480f, 0x420f0210480d, 0x490d8210480d, 0x420fc210400d, 0x108410fc210480d, 0x3d0d8210480d, 0x420d82105c12, 0x420d82d0480d, 0x4a0d8210480d, 0x4b0d8150480d, 0x360841f0480d, 0x4b0841203409, 0x360d0210480d, 0x360841203401, 0x4b0d8210440d, 0x450d8150480d, 0x420541203409, 0x360c4150480d, 0x360541203405, 0x450d8210480d, 0x36070150480d, 0x421041b0480d, 0x410d81c0480d, 0x410c4210480d, 0x400d8210480d, 0x360841a0480d, 0x4c0d81c0480d, 0x360a0210480d, 0x360bc210480d, 0x36084160480d, 0x210701203409, 0x440841203409, 0x210480d02405, 0x440d8210480d, 0x310841203409, 0x4d0c4210480d, 0x3a0d8210480d, 0x3e0d8210480d, 0x36084120340a, 0x36084120380d, 0x36084130480d, 0x360841203403, 0x360841203404],
  [0x420d8210480d, 0x10836084120340d, 0x420d82b08412, 0x108360ac210480d, 0x10836084190480d, 0x108360841203406, 0x108360a4210480d, 0x108360841203407, 0x1083b0d8210480d, 0x10836084120340b, 0x480d8210480d, 0x120420d8210480d, 0x10836084120340c, 0x10836084120480d, 0x420d8240840d, 0x10836090210480d, 0x108360c0210480d, 0x108360841203408, 0x1083f0d8210480d, 0x10836084120400d, 0x4b0d8210480d, 0x12c420d8210480d, 0x10836084120440d, 0x10836084210480d, 0x420d8150480d, 0x10836084150480d, 0x108410d8210480d, 0x108360841b0480d, 0x130420d8210480d, 0x360841c0480d, 0x108360841c0480d, 0x108360d8210480d, 0x420841203409, 0x108360841203409, 0x134420d8210480d, 0x360c4210480d, 0x108360c4210480d, 0x108420d8210480d, 0x360841203405, 0x108360841203405],
  [0x420d8210480d]]

def actT4 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x182000302000600, 0x182000302000600],
  [0x3d9d804b3700fa6201ec1803d82007b0200f600, 0x269d807f3701026201fc1803f82007f0200fe00, 0x2c1800582000b02001600, 0xc1800182000302000600, 0x59d800b3700b262002c1800582000b02001600, 0x19d80033700be62000c1800182000302000600, 0x59d800b3700d262002c1800582000b02001600, 0x19d80033700de62000c1800182000302000600, 0x60a, 0xc1800182000302000600, 0xcea0019c8011290006510040a000092800324800048000c1800182000302000600, 0x19a800334800068000c1800182000302000600, 0x19a800334802068000c1800182000302000600, 0x602, 0xc1800182000302000600],
  [0x69e000d2c00aa2800f41000610000c1800182000302000600, 0x60a, 0x34f001696007d14007a1400f41001e10003c1800782000f02001e00, 0x60a, 0x34f00169600551a00aa2801f41002a1000541800a82001502002a00, 0x60a, 0x1a640034a800675000ce400894800125000610000c1800182000302000600, 0x602, 0x1a740034d000692000cec0089a800131000610000c1800182000302000600, 0x602, 0x0, 0x2a0a, 0x0, 0x60e, 0x60e, 0x0, 0x60a, 0x0, 0x1e0a, 0x69d000cec0089a800f31000610000c1800182000302000600, 0xe9e00852c012a2800741000e620134c2008180007250096490000900038f40071d000e10001c1800382000702000e00, 0x1a7801f4e80609c002d2c00fa540204a003e8d007d1400fa1401f41003e10007c1800f82001f02003e00, 0x5a5001f3800a268013cc00019500032600423c, 0x1af00574800aa88014d0000195000326000e3c, 0x1d3c010a5800745004a820064740038e40001c000e10001c1800382000702000e00, 0x1d3c010a5800745004a820064740038e40101c000e10001c1800382000702000e00, 0x69e000d2c00aa2800f41004610008c1801182002302004600, 0x5a7800b4b00b28a002d0400598800b2680164a002c7402c8e40401c001610002c1800582000b02001600, 0xbac4000d78001a5005b42000674, 0x34e800691000cec00a9a800131000610000c1800182000302000600, 0x2d3c005a5802f45005a82009c9400592404024001610002c1800582000b02001600, 0xb4f00169600bd14016a0802725001610002c1800582000b02001600, 0x69e002d2c00aa2800f41001610002c1800582000b02001600, 0x1a780034b00be8a000d040019940033100064a000c7402f8e40501c000610000c1800182000302000600, 0x6c4000578005a700614200c674, 0x34f00069600bd14000a0800339000610000c1800182000302000600, 0xd3c001a5801545001e820004c400198405030000610000c1800182000302000600, 0x34f000696005514007a0800131000610000c1800182000302000600, 0x69e000d2c00aa2800f41000610000c1800182000302000600, 0x1e0a, 0x1e0a, 0xce99000d2a0059d400b3900166e0194c400994800125001610002c1800582000b02001600, 0x1e02, 0x69d000d34001a4800347001a82000cec0089a800131000610000c1800182000302000600, 0x1e02, 0x1ca140394100721000e41801c82003902007200, 0x0, 0x60e, 0x60e, 0x0, 0x60a, 0x0, 0x2a0a, 0x69d000cec00a9a802531000610000c1800182000302000600, 0x5a7800b4b00d28a002d0400598800b2680164a002c740348e40601c001610002c1800582000b02001600, 0xdac4000d78001a5006b46000674, 0x34e800691000cec0089a800f31000610000c1800182000302000600, 0x2d3c005a5802f45005a820104a400594406028001610002c1800582000b02001600, 0xb4f00169600bd14016a0804129001610002c1800582000b02001600, 0x69e002d2c00aa2800f41001610002c1800582000b02001600, 0x1a780034b00068a01bd040019b40033500065201bc740018e40701c000610000c1800182000302000600, 0x6c4004578005a700714600e674, 0x34f000696004514016a0800339000610000c1800182000302000600, 0xd3c001a5800f45002a820044c400198407030000610000c1800182000302000600, 0x34f000696005514007a0801135000610000c1800182000302000600, 0x69e000d2c00aa2800f41000610000c1800182000302000600, 0x2a0a, 0xea99000d2a0059d400b3900266a002ccc00894802925001610002c1800582000b02001600, 0x2a02, 0x69d000d34001a4801145000686000cec0089a800131000610000c1800182000302000600, 0x2a02, 0x24a340494500921001241802482004902009200, 0x804e00060a, 0x0, 0x60a, 0x0, 0x1a780034e81209c000d2c005a2800b41000610000c1800182000302000600, 0x60a, 0x1a780034b00069502812800aa2800f41000675000ce400894800125000610000c1800182000302000600, 0xd3a001a680034a800692000cec0019d40a03a00226a0004c400894800125000610000c1800182000302000600, 0xd3a001a680034a800692000cec0019d40a03a00f26a01dcc403694805d25000610000c1800182000302000600, 0x69e000d2c008a2802541000610000c1800182000302000600, 0x34d000699028130001a5400349000675000ce4008948003288180500004940019240b024000610000c1800182000302000600, 0xd34001a5400349000610000c1800182000302000600, 0x34e8002910005020059d801f350002650004c400593404f1c80021000041800082000102000200, 0x34e8022910045120059d80113680226a007cc40059540511d00221000441800882001102002200, 0x60a, 0x602, 0xd04e000602, 0x0, 0x1a780034b000695038128001a2800341000610000c1800182000302000600, 0x602, 0xd3a001a6800349000610000c1800182000302000600, 0x34f001696015d14000a140014100ee72000cca0149240531c80021000041800082000102000200, 0x34f00169600451a008a280574100f272000cda0099440551d00221000441800882001102002200, 0x602, 0x606, 0x60a, 0x602, 0x602],
  [0xd3e0402780034d80069701812c001a4c00347802a8b010114001a1c00f41804082000cee0019cc0033780226b000cce00698c00b2b802653002c9e00492c0071f800a3b000c2604804800308800010000c1e0380380030680000c000c1602802800304800008000c0e01801801102800004000c0600800800100800000, 0x2ce00058c00bae8003568002aa003d520102a000342801a81002cca00498400726800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x802780e04b01a08e02c1040880480100801e00e00401800182c0000500200803000c0080100a001002000, 0xd9c001b18003628260c4000d82001af801559001eaa048150001a740034c800676000ce40089b801135000666000cc40018500030800020e000c1800182000302000600, 0x1706702c0c6000d7a002ae801f5c82a0b8001564002aa80034a801691007512006a0400b3a800671006cd20049840112b000a550000a800294800127000a4d0000980029280191f000e3d05007800285000508000a0c000c1400282000502000a00, 0x7670042c6001d74012ac800356800eaa008d520d02a000342800e82001d020c820000332800e620084c20c018001929000e510500a0003934007250022490000900038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0x52ce00258c001b141d0620056c100257c004ac80295500069d001d320e02440033b0012750000e80049c80073700066a0004cc004994000320012620024a401393800b2683604c0024720048500090800060e00241800482000902001200, 0xb670016c600bd74016ac8003568016aa002d521002a000342801682002d020f82000273500166906c0d000599400b310006610000c000193400b250026490780900058f400b1d00023900007000585000b0800160c002c1000581000301001600, 0x1ace000d9a11833003164801ac600057c006ac80015500069e00353a00027000d4d001696001d24003a3800b4500028600350a00021000d410440720034d40009980033284206400347200685000309001a1000341800682000d02001a00, 0x3670006c6005574007ac8003568006aa000d521302a000145000689084110001a1400341000681000100001994003310006610940c0001934003250022490900900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1e9f0ac13c007a6c00f4b852096003d26019a3c00f4582a08a00050e01021400f41804082003cee0079cc00f3780666b003cce00098c02d2b806a5300b49e01492c0251f800a3b00dc2616004800f08804010003c1e15003800f0680400c003c1614002800f04804008003c0e13801803302804004003c0609000800100804000, 0x367001ecd000198007b2800f648040c8000d8c018b0800b5f0056ba00f56c00fac800157001ead000158007aa800f4f001e9a003d2c007a4800f4700768a003d0c01ca142d042001e82000c2c00785000109001e10003c1800782000f02001e00, 0x1b3800363002aba003d6401cac42d0580006ad000d54001aa400054000685000d020019940033080064d0044920018f40031d0002390000700018500030800060c000c1000181000301000600, 0x22ce00458c001ad401159002ab1010160019aa800346802289002cda0099a40112300224500008800890801120800040001c7c0028e80110a00221000441800181801102002200, 0x1902783004b05e08e09c1041980480300806200e00c01800182c000050060080b800c0180100a001006000, 0xd9c001b180036286a0c4000d82001af8015590680b0003d54001a740034c800676000ce40019b800335000266001cc40018500030800220e000c1800182000302000600, 0x26ce004d8c001b14380620086c1004d7c009ac80355500069d00fd321b82440033b0026750000e80099c80113700266d0000d80099a803f330006620104ac0059543602a00124a006c740098500130800060e004c1800982001302002600, 0xb670016c600bd74016ac8003568016aa002d521d82a000342801682002d021d0200041390016710d80e000599400b310006610000c000593400b250022490000900018f400b1d0052390e407000585000b0800160c002c1000581000301001600, 0x22ce000d9a1f0330045648022c600457c008ac80335500069e00453a0002700114d00169600fd24008a380114680008c00451401fa1800b4107a0720044dc0019b43c036001a620074740088500030900221000441800882001102002200, 0x3670006c6005574001ad4003590006b1104160007aa8011490006910f0120001a34003450006890001100019b4003350006691000d0001954003290022510000a00018f80011d0006390fc0700018500030800060c000c1000181800302000600, 0x2a9f11413c00aa6c0154b886096005526008a3c04046802a8b010114003a1c0154182a0820054ee00a9cc0153780226b0054ce00698c02f2b80265300bc9e00492c0071f800a3b011c262300480150880801000541e2200380150680800c0054162100280150480800800540e1a00180110280800400540605800801700808000, 0x367002acd00019800ab28015648080c8000d8c022b0800b5f0086ba00456c00aad40005a002ab2001d5c00faa80154f002a9a00552c00aa480154700928d11c11800aa2801543007682000c2c00a85001109002a1000541800a82001502002a00, 0x1b3800363002aba0125722382e00035a8006b2000d620002c000f5500068d000d120019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0x6ce000d7c001af40605e0006b9005564007aa80034a800691000cbc0019740002e00065a000cb200016000b2b002652002c9c0049280030a000610000c1400182000302000600, 0x2502784804908408a0a01042580480500809200e01401800182c0000500a0080b800c0280100c00100a000, 0xd9c001b184d0620006bd000d74001ae44c05c002ab2003d54001a5400348800675000ce200895800b2900024e002c940018500030800060c000c1400182000302000600, 0x3670006cd144198001b24003630006c5140188001af80035e89e0bc005564007aa80034f00069d000138001a680034b000695000128001a4800747007e8a00fd0c003a080033b0006751380e81e81a82203106e05207009400185000309000610000c1800182000302000600, 0x3670006c6000d7c001af45205e0006b9005564007aa80034d000699138130001a54003490006910001200019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x1b38003668000cc000d94001b18003610006be000d7a0002f00035d0016b6010d64005ab802b5500069e000d2c001a545304a002a8a003d040018580030a000610000c1800182000302000600, 0x34f80069b13c132001a5c5204a800693000d1e008a2c00343800283000cee0301d40033980c072002cde0099ac00b33801263000cae00894c5502900064f0004962a01280211f82c03b000c262b80480030880c010000c1e2680380030680c00c000c162b00280030480c008000c0e1780180110280c004000c060680080010080c000, 0x1b38003650006c6000d84001b04530600006be000d7a0302f00035d0006b9000170001ad8015590006ae003d54001a640034a800691000cea0019c800338800070000cac0089480032700024a000c2c0018500030800060c000c1400182000302000600, 0x6c6000d8a040310003608006be005564007aa80033f00067d0000f80019e80033c800078000cec0019c80033700226a000ccc0069880030a00060e000c1800182000302000600, 0x2b82784404905408a1601042c80480700809200e01c0181880280700401e00601c00800180c0000100e000, 0xd9c2d833000363002aba003d64001ab4003550006a9168150001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600, 0x1b38003668000cc000d94001b18003628000c4000d84001af80035d0006b6011564001ab80315500069e000d3a2e02700034b002a8a003d040018580030a000610000c1800182000302000600, 0x34f81009d000d360402680034b800693140124001a3c011458006870035060019dc5203b000673000cde0089ac5e0350006670004c62e818800b2b802653002c9e01492c0071f82e03b000c262d804800308810010000c1e2f80380030681000c000c1625002800304810008000c0e19001801102810004000c0608000800100810000, 0x1b38003650006c9170190001b18003628100c4000d84001b04000600006be000d74001ad8015590006ae003d54001a740034d000699000130001a480033b000672000cdc0089a800333000262000c2c0018500030800060e000c1800182000302000600, 0xd4c001a94000520006a2000d420002800034f00069a000d2c001a4800347002a8a000d0c007a0800309000610000c1800182000302000600, 0x318214620328c20491800722c80480900809600e0240181980280900402200602400800180c00001012000, 0x6ce000d8c008ae8001590006ad000d52001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600],
  [0x9013e1182782204d83c09707412c0e024c1604782a08b05011406021c0b04181408206c0ee0d01cc1303782406b0240ce04018c1102b82005301c09e03012c0501f80803b09c0261300482500880001008401e1000381f00680000c0640160c00281700480000803c00e0700180d00280000400c00601000801000800000]]

def witT4 : List ℕ := [0x18030001a0641d, 0xc000181d06819, 0x58130001b06825, 0x18000582506c1a, 0x280004c250681b, 0xc000201e06c19, 0x28000582506c1a, 0x400004c1d06819, 0x180000c1d0641a, 0x200000c1e0641b, 0x340304c1d06819, 0x4c030341a0641d, 0x1800058250781d, 0x280304c250741e, 0x2803058250781d, 0xc0004c1d06819, 0x200004c250681b, 0x400d0181d06819, 0x4c000582506c1a, 0xc00058250781d, 0x20030001b0641e, 0x40000181d06819, 0x40000581e06c19, 0x34030581e06c19, 0x40000201e06c19, 0x4c000401d0641a, 0x58000401e0641b, 0x400004c2a06819, 0x40000001906419, 0x400d04c1d06819, 0x18000401d0641a, 0x1803058250781d, 0xc000582506c1a, 0x34030181d06819, 0x34030201e06c19, 0x340304c2707419, 0x34000001906419, 0x200004c250641b, 0x1800058250641a, 0x4c0a00c1e06425, 0x4c0a0001b06425, 0x580a00c1d06425, 0x580a0001a06425, 0xc000581e06c19, 0xc030281b06c19, 0xc000582507819, 0x18030001a0641e, 0xc030281a06819, 0xc0004c2507419, 0xc000181d06c19, 0x4c000282506c1a, 0xc000201d06c19, 0x281e07819, 0xc000582506c19, 0x180000c1d0641b, 0x281d07419, 0xc0004c2506819, 0xc000181e06819, 0xc000201e06819, 0x18030001b0641e, 0x180000c1e0641b, 0x18000582506c19, 0x4c000582506c19, 0x200004c2506819, 0x580004c2506819]

def S4 (s i : ℕ) : List ℕ := unpackW wdT4 9 ((levT4.getD s []).getD i 0)

def N4 (s : ℕ) : ℕ := (levT4.getD s []).length

def A4 (s i tag : ℕ) : ℕ := findAct 4096 ((actT4.getD s []).getD i 0) tag

def W4 (w : ℕ) : ℕ := witT4.getD w 0

def Z4 (s : ℕ) := barrier 25 S4 N4 A4 W4 idRot s

theorem enc_inputs4 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT4) = xsT4 := by decide +kernel

theorem enc_goal4 : encL fT4 rowsT4 = goal 25 := by decide +kernel

theorem mask4 : mask 25 = 2 ^ rowsT4.length - 1 := by decide +kernel

theorem proper_fail4 : ∀ zs ∈ xsT4.sublists, zs ≠ xsT4 → (cov 25 zs &&& lo 25) ≠ lo 25 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked4 : ∀ s ≤ 7, ∀ i < N4 s, Z4 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun4 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 25) (goal 25) s xsT4) : False := by
  have hc : NatRun (mask 25) (goal 25) 7 xsT4 := extend_run h hs
  have p : xsT4.Perm (S4 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked4 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub4 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT4 → NatRun (mask 25) (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT4
  · subst e; exact noRun4 s hs h
  · exact proper_fail4 zs (List.mem_sublists.2 hz) e (required h)

theorem low4 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT4 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT4 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 25) (encL fT4 rowsT4) s' (ws.map fun a => encL a rowsT4) :=
    Run.map (fun a : BFn 5 => encL a rowsT4)
      (fun a => by rw [mask4]; exact encL_inv a rowsT4)
      (fun a b => encL_and a b rowsT4) (fun a b => encL_or a b rowsT4) hrun
  rw [enc_goal4] at hr
  refine no_sub4 s' (by omega) _ ?_ hr
  rw [← enc_inputs4]
  exact hsub.map _

def mono4 : List Gate := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.and, [3, 8]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [6, 11]⟩]

theorem mono_ok4 : ∀ g ∈ mono4, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono4, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval4 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono4, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve4 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfee8eee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono4, 12, mono_ok4, ?_, mono_eval4⟩
  by_contra hlt
  have hlen : mono4.length = 8 := rfl
  apply low4
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT5 : List ℕ := [0, 2, 4, 6, 6, 6, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 1, 3, 5, 7, 14, 22, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT5 : List ℕ := [0x93267800000, 0x12e5dd01c3ba, 0x274e9e0e1c3c, 0x3c8fe8701fc0, 0x3ff9107fe000]

abbrev fT5 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT5 : List ℕ := [0x488001fff, 0x6ef801fff, 0x2045000000, 0x10206000000, 0x240100fe03f, 0x2449c000038, 0x370178fe03f, 0x80260000000, 0x93000000000, 0x93267800000, 0x936ef801fff, 0xb72778fe03f, 0x10810071e3c3, 0x1085c8000380, 0x12c59801c3ba, 0x12c5dc0003b8, 0x12e11001c000, 0x12e59c01c038, 0x12e5d801c380, 0x12e5dd01c3ba, 0x13e7df01c3ba, 0x18b161f1e3c3, 0x19b367f1e3c3, 0x1ae7fd01c3ba, 0x1bf5dd01c3ba, 0x1bf7ff81c3ba, 0x2408007e3c45, 0x240e88001c00, 0x264c980e1c3c, 0x264e9c001c38, 0x2748100e0000, 0x274c9c0e0038, 0x274e980e1c00, 0x274e9e0e1c3c, 0x276edf0e1c3c, 0x2d1a22fe3c45, 0x2d3a67fe3c45, 0x2f4efe0e1c3c, 0x2f7e9e0e1c3c, 0x2f7eff8e1c3c, 0x348d88701fc0, 0x348fc8001f80, 0x36c9107fe000, 0x36cd987fffff, 0x37e9100fc000, 0x37efdf0fdfbe, 0x3c8900700000, 0x3c8dc8700380, 0x3c8f88701c00, 0x3c8fe8701fc0, 0x3cafed701fc0, 0x3d8fee701fc0, 0x3dbfe8701fc0, 0x3dbfeff01fc0, 0x3ee91071c000, 0x3eeffd71dffa, 0x3fc9107e0000, 0x3fcffe7e1ffc, 0x3ff9107fe000, 0x3ff9557fe000, 0x3ffb167fe000, 0x3ffb707fe000, 0x3ffb77ffe000, 0x3ffddd7fe3ba, 0x3fff9e7ffc3c, 0x3ffff87fffc0]

def levT5 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0xec360a01a, 0xfc320a01a, 0xfc360881a, 0xfc360a014, 0xec2a02806, 0xc82d02806, 0x3b0700e02806, 0x3207c1102806, 0xec1e0380a, 0xdc220380a, 0x2f088110380a, 0xc8200440a, 0xc0220440a, 0xec1c0400a, 0xe41c0500a, 0x2f07c1c0500a, 0xc81f0480a, 0xc41f0500a, 0xbc2204c0a, 0xbc210500a],
  [0x3b0c8220500a, 0x3b0c82c08814, 0x3b0c8220680a, 0x3b0c8280500a, 0x3b0d8220500a, 0x3f0c8220500a, 0x3b0c8240880a, 0x3b0c8160500a, 0x3b0881402807, 0x320881402802, 0x3b0c82c09022, 0x3b0c82c0880f, 0x3b0c82c05814, 0x3b0c82c07414, 0x3b0b02908814, 0x320b02b08814, 0x3b0b02205007, 0x320b02205002, 0x3b0c82c0881a, 0x3b0c82c0a014, 0x3b0d82c08814, 0x3f0c82c08814, 0x3b0c82203c0a, 0x3b0c81d0500a, 0x3b0a4220500a, 0x320ac220500a, 0x3b0c8280680a, 0x3b0d8220680a, 0x3f0c8220680a, 0x3b0c82206c0a, 0x3b0c81a0580a, 0x3b0881a02807, 0x320881a02802, 0x3b0c82206803, 0x3b0c8230500a, 0x3b0cc220500a, 0x3c0c8220500a, 0x3b0d8280500a, 0x3f0c8280500a, 0x3b0c8280900a, 0x3b0c8140340a, 0x3b0a01402807, 0x320a01402802, 0x3b0c82805004, 0x3b0c8220540a, 0x3b0d0220500a, 0x3d0c8220500a, 0x3f0d8220500a, 0x3b0d8240880a, 0x3b0d8160500a, 0x3b0881402805, 0x360881402802, 0x3b0d82205008, 0x3b0c8220600a, 0x3b0c8260500a, 0x3e0c8220500a, 0x3f0c8240880a, 0x3f0c8160500a, 0x3f0881402807, 0x320881402801, 0x3f0c82205009, 0x3b0c8220640a, 0x3b0c8270500a, 0x3b0d4220500a, 0x3b0c8250880a, 0x3b0c8240580a, 0x3b0902202807, 0x320902202802, 0x3b0c82e02806, 0x3b0a8220500a, 0x320b4220500a, 0xec320880e02806, 0xec320881102806, 0xec320701402806, 0xec3207c1402806, 0x3b0e0220380a, 0x3b0c81e0500a, 0x370c8220500a, 0xec32088110380a, 0xec22070140380a, 0xec2f088140380a, 0x400c8220440a, 0x3b0c8200500a, 0x3b0c0220500a, 0xc82207c140440a, 0xc82f088140440a, 0x3b0c8170500a, 0x3b0581402807, 0x320581402802, 0x3b0c8220400a, 0x3b0e81c0500a, 0x390c8220500a, 0xec3207c1c0500a, 0xec2f0881c0500a, 0x3b0c8220480a, 0x410c81f0500a, 0x3b0c4220500a, 0xc82f0881f0500a, 0x3b088140300a, 0x220500a01c02, 0x3b0c82204c0a, 0x3b0c8210500a, 0x420bc220500a, 0x320881402c0a],
  [0x3b0c8220500a, 0xec32088140280a, 0x3b0c82c08814, 0xec320b0220500a, 0x3b0c8220680a, 0xec320881a0500a, 0xec320881402803, 0x3b0c8280500a, 0xec320a0220500a, 0xec320881402804, 0x3b0d8220500a, 0xec360c8220500a, 0xec320881402808, 0x3f0c8220500a, 0xfc3b0c8220500a, 0xec320881402809, 0xec32088140500a, 0x3b0c8240880a, 0xec32090220500a, 0xec320b8220500a, 0xec320881402806, 0xec380c8220500a, 0xec32088140380a, 0x1003b0c8220500a, 0xec32088140440a, 0xec32088220500a, 0x3b0c8160500a, 0xec32088160500a, 0xec3a0c8220500a, 0xec320881c0500a, 0x1043b0c8220500a, 0xec320881f0500a, 0xec320c8220500a, 0x3b0881402807, 0xec320881402807, 0x1083b0c8220500a, 0xec320bc220500a, 0xec3b0c8220500a, 0x320881402802, 0xec320881402802],
  [0x3b0c8220500a]]

def actT5 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0xbc1801782002f02005e00, 0xcc1801982003302006600, 0xdc1801b82003702006e00, 0xe41801c82003902007200, 0x389a80712900e23901c4180388200710200e200, 0x1e9a803d29007a3900f41801e82003d02007a00, 0x389c00713000e648, 0x1e9c003d3000c648, 0x389880712500e23a01c4180388200710200e200, 0x2698804d25009a3a01341802682004d02009a00, 0x26a4004d4400d250, 0x1e98803d25007a3a00f41801e82003d02007a00, 0x2698804d25009a3a01341802682004d02009a00, 0x399880732500e63a01cc180398200730200e600, 0x2d98805b2500b63a016c1802d82005b0200b600, 0x2da6005b4800d670, 0x319880632500c63a018c180318200630200c600, 0x2d98805b2500b63a016c1802d82005b0200b600, 0x349880692500d23a01a4180348200690200d200, 0x3598806b2500d63a01ac1803582006b0200d600],
  [0x2820004c40009280011d00021000041800082000102000200, 0x20a, 0x1410002620004940008f40011d00021000041800082000102000200, 0x14100026200049a0009280011d00021000041800082000102000200, 0x1410002650004c40009280011d00021000041800082000102000200, 0x1428002820004c40009280011d00021000041800082000102000200, 0x20a, 0x20a, 0x202, 0x202, 0x0, 0x20a, 0x0, 0x20a, 0x20e, 0x20e, 0x0, 0x0, 0x20a, 0x20a, 0x20a, 0x20a, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0xa08025408020800004c40119840003000024d0004940008f40011d00021000041800082000102000200, 0xa08029408040800004ca00098800125004e490000900008f40011d00021000041800082000102000200, 0xa140014100026200b4c2010180001250056490040900008f40011d00021000041800082000102000200, 0x206, 0x206, 0x202, 0x202, 0xd41001a620034940068f400d1d001a1000341800682000d02001a00, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0xa08031408060800004ca0009880012680024a0004740178e40001c00021000041800082000102000200, 0xa140014100026200d4c20181800012680024a0004740198e40101c00021000041800082000102000200, 0x206, 0x206, 0x202, 0x202, 0xf41001e62003c9a00792800f1d001e10003c1800782000f02001e00, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0xa14001410002650004c40009280392480604800047401b8e40201c00021000041800082000102000200, 0x20a, 0x20a, 0x202, 0x202, 0x11410022650044c40089280111d00221000441800882001102002200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x20a, 0x20a, 0x202, 0x202, 0x1342802682004cc40099280131d002610004c1800982001302002600, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x2820004c40009280011d00021000041800082000102000200, 0x20a, 0x0, 0x0, 0x0, 0x29600f52a0282500014500027600ecea0201d00013500025200049a0009280011c80021000041800082000102000200, 0x5040009880012b002a550100a80009280011d00021000041800082000102000200, 0x5040009880012b002a550140a80009280011d00021000041800082000102000200, 0x1813801fa0004138000648, 0x1c188021aa004538000648, 0x18128023a0000138000260, 0x1c178024aa000138000260, 0x29e01353a048270001410096760004ea0401d00013680026a0004c40009280011d00021000041800082000102000200, 0x5040009b80193681006c0004c40009280011d00021000041800082000102000200, 0x5040009b80193681206c0004c40009280011d00021000041800082000102000200, 0x28198027ac005148000a50, 0x18128001a2000138000268, 0x28178029ac000148000288, 0xae9e00053a0602700554b00029502c128000a34001450002820004c40009280011d00021000041800082000102000200, 0x51c01ea340b0460002820004c40009280011d00021000041800082000102000200, 0x51c026a340c0460002820004c40009280011d00021000041800082000102000200, 0x1c128001a2000138000268, 0x28178002ac000148000288, 0x20a, 0x0, 0x0, 0xd040019d801d3a81a074000cc40019280031d000610000c1800182000302000600, 0x69e016d3a07027000341000675000ce402c9b80033681a06c000cc40019280031d000610000c1800182000302000600, 0xd040019d801d3a81c074000cc40019280031d000610000c1800182000302000600, 0x3c19802eae005f4c000a70, 0x3c188030ae00034c000690, 0xd2c031a541004a000682000cc40019280031d000610000c1800182000302000600, 0xce9e000d3a0882700034a80069201951c001a3410046000682000cc40019280031d000610000c1800182000302000600, 0xd2c02da541104a000682000cc40019280031d000610000c1800182000302000600, 0x3c188002ae00034c000690, 0x206, 0x0, 0x153c034a741204e000a820014c40029280051d000a1000141800282000502000a00, 0x153c035a741304e000a820014c40029280051d000a1000141800282000502000a00, 0xa9d001534037a580054a82609401b51c002a3412046000a820014c40029280051d000a1000141800282000502000a00, 0x206],
  [0x153e002a6c0034b80069300051e000a2c001438002830141040059dc0033980126f0004d600099c00531808062001cae00094c0012780064b00c0940008fc0011d80403a0004260480480010880001000041e0400380050680000c0004160380280030480000800040e0300180010280000400040600800800100800000, 0x55a000aa80015480a0a800050a000a08005408080800004ca0009880033080606000049a0009280012480404800046c0008d40001a0002320004620000c00010a00021000041800082000101000200, 0x782580e03b01a05502c09a0880480100802000e00401800082c0000500200803000c0080100a001002000, 0x2c600058a0c8310001608002aa054150000a780054e83009c000532000a08140400006760004ea0b81d00013900026e0004da0b01b0001350002660004c40009281302400023a0480700008500010800020e00041800082000102000200, 0xa9f001536001a5c0034980028f000516000a1c00141838082002cee0019cc0093780026b0004ce00298c1b031000e570004a600093c0032583404a00047e0100f40011d80403a0004261000480010880401000041e0f80380050680400c0004160f00280030480400800040e0e80180010280400400040609000800100804000, 0x2bd000572000ad4001588002aa00252a000a44009468002890005040039d400138800e6d0004d20009880012b0002550000a80009480012880405000049c0009340002600024a00047c0068f42101e00023a0004280008400010600020a00041000081800102000200, 0x2b200055a000aa8001548480a8000514000a1400141000a8108c1000009a800132800262000cc211018000129001a510840a0000934001250002490000900008f40011d0002390000700008500010800020c00041000081000101000200, 0xa9f001536001a5c0034980028f000516000a1c0014184c082002cee0019cc0093780026b0004ce00298c25031000e570004a600093c0302680064b00c0940008fc0011d83403a0004261500480010880601000041e1480380050680600c0004161400280030480600800040e1380180010280600400040609800800100806000, 0x6c5000d82001af40035c8006aa002d3a001a6400b4a800691000d040019d80033a800074000ce40019c403038000e6e0004d400099800332800064000cc40039580012900024e003c9a1581300032500063a000c280018400010700060c00041400182000302000600, 0x2b200055a000aa80015485c0a8000514000a1400141000a810b41000009a800f348560680004ca000988003308000600004a4000934001250002490b00900008f40011d0002390000700008500010800020c00041000081000101000200, 0xa9f001536001a5c0034980028f000516000a1c0014185e082002cee0019cc0093780026b0004ce02019400531808062001cae00094c0012780064b0940940008fc0011d83603a0004261980480010880801000041e1900380050680800c0004161880280030480800800040e180018001028080040004060a000800100808000, 0xacd001592002b1400560800aaa00153c002a740004e000a9a00153202026000b4b00069200251c000a2800143000a85000108002a0800b3b0006720024dc0009a8001330022650d00c800298800525000a3a0014280008480050800020e00141800282000502000a00, 0x2b200055a000aa80015486e0a8000514008a2434044000285000504002a040004000026a0004ca0009880033086c0600004a4000934001250002490d40900008f40011d0002390000700008500010800020c00041000081000101000200, 0xa9f001536001a5c0034980028f000516000a1c050428002830141040059dc0033980126f0004d600099c0053185e062001cae00094c0012780064b0980940008fc0011d83803a0004261d80480010880a01000041e1d00380050680a00c0004161c80280030480a00800040e1c00180010280a0040004060a80080010080a000, 0x2ce00059a000330001650002c9014190002b18005610006be000d74000ad8001590002ae00055a0002b000155000a9e001534001a580034900028e000514000a18013428780840005040009880012500023a00042c0008500010900021000041800082000102000200, 0x2b2004d621e02c0001568002aa0005520002a000145000285000504002a043f04000026a0004ca0009880033087c0600004a4000934001250002490f40900008f40011d0002390000700008500010800020c00041000081000101000200, 0xad4001588002aa00251a000a2400141000e6d0004d2000988001230002450000880009080012080004000047c0008e80010a00021000041800081800102000200, 0x1c02083003108004a09c0742180480600808400e01801800082c0000500c00810400c0300100a00100c000, 0x2c5000582000aa80014e800a990005040009d80033900026e0004d40009980013100024a0004740008500010800020e00041800082000102000200, 0x58c000b14460620002c1000554000a780094e88a09c000532000a080033b0002750000e80009c80013700026d0000d80009a8001330002620004ac00a9544402a00024a0004740008500010800020e00041800082000102000200, 0x12818a2402f400759000aad005d522482744704a800e8a005d0a002a0400139002a711100e00039a800732800e62000cc200018000729000e4d001c940009240002400023d001c7200385000708000e0c001c1000381000101000e00, 0x59c000b344d0660002c9000554002a780014e80009c000534003a580014a898094000524000a380014680008c000514000a180014100026e0064da2581b00013100024a0004740008500010900021000041800082000102000200, 0x14019a2702f40035a802eb10025542782780014900329112c120004a3400945000a89000110004a084703a802e6d000cd20049880092a8012520004a20001400092500023e0024740048500090800120c00241000081800902001200, 0x59c000b34000660002ca00258c000b14530620002c2001d7c000af45205e0002ba00056c000ad40005a0002b200055c000aa80014700028d144118000a080013100024a0004740008580010a00021000041800082000102000200, 0x15419c2a03180015d0002b9144170000ad4001590002b1000160000aa84e04a80068d001512000a084803a800a6d000cd20009880012a8002520004a20001400012500023e0004740008500010800020c00041000081800102000200, 0x1af40035c8006aa002d2a001a440034100065e000cba0001700032d0006590000b00039580012900024e000c940018e80030a00061000041400182000302000600, 0x1c8208310310ac04a0780742c0048070080ae00e01c01800082c0000500e00810400c0380100c00100e000, 0x2bd000572000aa80034a800a910005040009d4001388002620004ac0009480012700024a0004740008500010800020c000c1400082000102000200, 0xd9c001b345b0660002c9000d54002a780034e80009c000d34001a580034a800094000d2400da38003468b208c000514000a18003410006760074ea2d01d00033100064a000c7400185000109000610000c1800182000302000600, 0x17419a2e03140015e802eb9002d54001a6801d4c8b4098002d2a005a480054880009013c11c005a0800b3a801672000ce20001c049037001662005cac0009480012700164a002c7400585000b0800160c00041400582000b02001600, 0x59c001b34000660006ca002d8c001b14600620002c2000d7c001af40005e0006ba006d6c001ad45e05a0002b200055c001aa80034b00069517c128001a080033100064a000c740008580030a000610000c1800182000302000600, 0x18419c001b08003608be0c0000d7a001ae80015c8000b815016c001aa85c04e800295001522001a080033a800672000ce20001c04a0370006620014ac0009480012700064a000c740018500030800060c00041400182000302000600, 0x2b1400560800aaa0014fc0029f40003e000a7a0014f20001e000b3b0006720024dc0009a800133000a620014940028e80050a00020e00141800282000502000a00, 0x1d02282903503e052188072318048080080ae00e0200182100280800402000602000800080c00001010000, 0x2b200055a000aa4001450002850005020009a8003328006610004a40009340012480023d0004720008500010800020c00041000081000501000200, 0x59c002b3400066000aca00158c002b1400062000ac200857c002af46505e0002ba007d6c002ad46405a0002b200055c002aa80054f000a9d198138002a0800531000a4a0014740008580050a000a1000141800282000502000a00, 0x1594002b2466064000ac5001584000b04000600c20be15416c002aa80054e800a9a0015320002605d04b0a008e0015040009d80033900066e0004d400099800531000a4a0014740028500050800020e00141800282000502000a00, 0xa98001528000a4000544000a8400050000a9e001534001a580034900028e000514000a18001410002620004940008e80010900021000041800082000102000200, 0x1982282a03504005219c072318048090080b000e0240182180280900402200602400800080c00001012000, 0x2b200055a000aa400145000a850015020009a8003328006610004a40009340012480023d0004720008500010800020c00041000081000101000200],
  [0x9013e11826c1f04b83c09306011e0b822c0f04381c0830341040e81dc1c03982c06f0540d606019c0b0318140620500ae09814c0902781004b01c0940300fc0501d80803a09c0261300482500880001008801e1080382000680000c06c0160d00281900480000804800e0880181000280000400c00601000801000800000]]

def witT5 : List ℕ := [0x1c03038200701b, 0x2803044230701b, 0x2807050230801b, 0x380700c1c06c20, 0x380301c2006c1c, 0x44030282306c1c, 0x4000001705c17, 0x8000001705c17, 0x18000001705c17, 0x34000001705c17, 0x2803044200701b, 0x440e050230801c, 0x2807050200701b, 0x440a00c1c06c23, 0x2807050230701b, 0x500a01c2006c23, 0x50070282306c20, 0x28070502308017, 0x440e0502308017, 0x28030442307017, 0x500e0442307017, 0x44030282306c17, 0x50070282306c17, 0x1c030382007017, 0x50110382007017, 0x380301c2006c17, 0x500a01c2006c17, 0x380700c1c06c17, 0x440a00c1c06c17, 0x340301c2006c1c, 0x1803038200701b, 0x1c03050200701b, 0x1c03044200701b, 0x5003038200701b, 0x2803038200701b, 0x2803050230701b, 0x5003044230701b, 0x340700c1c06c20, 0x1c02038200701b, 0x4407038200701b, 0x2807038200701b, 0x4407050230801b, 0x380600c1c06c20, 0x380201c2006c1c, 0x340a00c1c06c23, 0x2801044230701b, 0x380a044230701b, 0x2807044230701b, 0x380a050230801b, 0x1803044230701b, 0x440600c1c06c23, 0x44010282306c1c, 0x1c02050230801b, 0x2801050230801b, 0x500201c2006c23, 0x50010282306c20, 0x1c03034200701b, 0x2803034230701b]

def S5 (s i : ℕ) : List ℕ := unpackW wdT5 9 ((levT5.getD s []).getD i 0)

def N5 (s : ℕ) : ℕ := (levT5.getD s []).length

def A5 (s i tag : ℕ) : ℕ := findAct 4096 ((actT5.getD s []).getD i 0) tag

def W5 (w : ℕ) : ℕ := witT5.getD w 0

def Z5 (s : ℕ) := barrier 23 S5 N5 A5 W5 idRot s

theorem enc_inputs5 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT5) = xsT5 := by decide +kernel

theorem enc_goal5 : encL fT5 rowsT5 = goal 23 := by decide +kernel

theorem mask5 : mask 23 = 2 ^ rowsT5.length - 1 := by decide +kernel

theorem proper_fail5 : ∀ zs ∈ xsT5.sublists, zs ≠ xsT5 → (cov 23 zs &&& lo 23) ≠ lo 23 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked5 : ∀ s ≤ 7, ∀ i < N5 s, Z5 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun5 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 23) (goal 23) s xsT5) : False := by
  have hc : NatRun (mask 23) (goal 23) 7 xsT5 := extend_run h hs
  have p : xsT5.Perm (S5 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked5 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub5 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT5 → NatRun (mask 23) (goal 23) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT5
  · subst e; exact noRun5 s hs h
  · exact proper_fail5 zs (List.mem_sublists.2 hz) e (required h)

theorem low5 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT5 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT5 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 23) (encL fT5 rowsT5) s' (ws.map fun a => encL a rowsT5) :=
    Run.map (fun a : BFn 5 => encL a rowsT5)
      (fun a => by rw [mask5]; exact encL_inv a rowsT5)
      (fun a b => encL_and a b rowsT5) (fun a b => encL_or a b rowsT5) hrun
  rw [enc_goal5] at hr
  refine no_sub5 s' (by omega) _ ?_ hr
  rw [← enc_inputs5]
  exact hsub.map _

def mono5 : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [8, 11]⟩]

theorem mono_ok5 : ∀ g ∈ mono5, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono5, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval5 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono5, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve5 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeaaa (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
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

def rowsT6 : List ℕ := [1, 1, 1, 1, 2, 2, 4, 4, 8, 10, 10, 10, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 5, 9, 17, 3, 6, 5, 6, 9, 11, 14, 26, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT6 : List ℕ := [0x9326be00000f, 0x12e5d62070e30, 0x274e9c43870c0, 0x3c8fe09c07f00, 0x3ff9011ff8000]

abbrev fT6 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT6 : List ℕ := [0x0, 0x1e60000ff, 0x400000000, 0x62a000f3f, 0x2000000000, 0x228c0071cf, 0x26ae00000f, 0x26ae007fff, 0x4800000000, 0x4940007ff0, 0x49e6007fff, 0x4d62000e30, 0x4f6a007fff, 0x69c40070c0, 0x6bcc007fff, 0x6e08007f00, 0x6eae007f0f, 0x6fee007fff, 0x20000000000, 0x20422000000, 0x26fee007fff, 0x3003207803f, 0x100000000000, 0x102084000000, 0x106fee007fff, 0x1100943880cf, 0x1224a6000000, 0x1300b600000f, 0x1300b63f80ff, 0x240000000000, 0x2401403f80f0, 0x2401e63f80ff, 0x244940000000, 0x246fee007fff, 0x246fee3fffff, 0x260162070030, 0x264d62000000, 0x2701723f80ff, 0x3401c43800c0, 0x3469c4000000, 0x3501d43f80ff, 0x3700103f8000, 0x3700b63f800f, 0x3701f63f80ff, 0x3705f63f80ff, 0x3721f63f80ff, 0x3749f63f80ff, 0x3749f63fffff, 0x376e183fff00, 0x376ffe3fffff, 0x800000000000, 0x802608000000, 0x806fee007fff, 0x810219c0810f, 0x82262a000000, 0x83063a00000f, 0x90268c000000, 0x91229c00000f, 0x930010000000, 0x930432000000, 0x932094000000, 0x932618000000, 0x9326be00000f, 0x934950007ff0, 0x936ebe00000f, 0x936ffe007fff, 0xa427483f80f0, 0xa54b59c0810f, 0xb701f63f80ff, 0xb726be00000f, 0xb727fe3f80ff, 0xb76ffe00000f, 0x1081000000000, 0x1081001c78f30, 0x108162bc78f3f, 0x1085c00000e00, 0x10a1422070e30, 0x10a5c22000e00, 0x10b1033c78f3f, 0x1183085c78f30, 0x1195c94388ecf, 0x12c5940070e30, 0x12c5d40000e00, 0x12c5d62070e30, 0x12e1000070000, 0x12e1422070000, 0x12e328c0771cf, 0x12e5940070000, 0x12e5962070e30, 0x12e5c00070e00, 0x12e5d62000e00, 0x12e5d62070000, 0x12e5d62070e30, 0x12e7d62070e30, 0x12e7fee077fff, 0x13e5d62070e30, 0x13e7de6070e30, 0x13f5df63f8eff, 0x1881609c00f00, 0x1887e08000e00, 0x1891219c78f3f, 0x18b1011c78000, 0x18b163bc78f3f, 0x18b363bc78f3f, 0x18b79d5c7f0c0, 0x18b7fffc7ffff, 0x19b163bc78f3f, 0x19b36be00000f, 0x19b36bfc78f3f, 0x19b7ebe000e0f, 0x1ae5d62070e30, 0x1ae7f6a070e30, 0x1af5f7bc78f3f, 0x1bc17cdf80fc0, 0x1bd7bdc070e3f, 0x1be7fee070e30, 0x1bf1010070000, 0x1bf17ffff8fff, 0x1bf36be07000f, 0x1bf5d72070e30, 0x1bf7df6070e30, 0x1bf7f7a070e30, 0x1bf7ffe070e3f, 0x2408000000000, 0x2408001f8f1c0, 0x240a28df8f1cf, 0x240e800007000, 0x2428423f8f1c0, 0x243e83207f03f, 0x250a0843870c0, 0x250e884007000, 0x2518095f8f1cf, 0x264c9403870c0, 0x264e940007000, 0x264e9c43870c0, 0x2748000380000, 0x274862a380f3f, 0x274a084380000, 0x274c940380000, 0x274c9c43870c0, 0x274e800387000, 0x274e9c4007000, 0x274e9c4380000, 0x274e9c43870c0, 0x274edc43870c0, 0x274efee387fff, 0x276e9c43870c0, 0x276ede63870c0, 0x277e9f63ff0ff, 0x2c0a209c07100, 0x2c0ee08007000, 0x2c18219f8f1cf, 0x2d18011f88000, 0x2d1a29df8f1cf, 0x2d1a69df8f1cf, 0x2d1cd73f88e30, 0x2d1effff8ffff, 0x2d3a29df8f1cf, 0x2d3a6be00000f, 0x2d3a6bff8f1cf, 0x2d3eebe00700f, 0x2e6a36bc77130, 0x2e7cf7a3870cf, 0x2f4e9c43870c0, 0x2f4efcc3870c0, 0x2f5ebddf8f1cf, 0x2f6efee3870c0, 0x2f78010380000, 0x2f7a3fffff1ff, 0x2f7a6be38000f, 0x2f7e9d43870c0, 0x2f7edf63870c0, 0x2f7efdc3870c0, 0x2f7effe3870cf, 0x3489001fffff0, 0x348d801c07f00, 0x348fc00007e00, 0x348fe09c07f00, 0x35ab4a63f7ef0, 0x35bd8b7c07f0f, 0x36c9001ff8000, 0x36cb6afff800f, 0x36cd941fffff0, 0x36cffefffffff, 0x36edd62070e30, 0x36edd63fffff0, 0x36efd62077e30, 0x37cf9c43870c0, 0x37cf9c5fffff0, 0x37cfdc4387ec0, 0x37e90003f0000, 0x37edd623f0e30, 0x37ef9c43f70c0, 0x37efde63f7ef0, 0x37f9011ff8000, 0x37fd9f7ffffff, 0x3c89001c00000, 0x3c891e7c000ff, 0x3c89609c00f00, 0x3c8b209c07100, 0x3c8b609c00000, 0x3c8b609c07f00, 0x3c8dc01c00e00, 0x3c8de09c07f00, 0x3c8f801c07000, 0x3c8fa09c07f00, 0x3c8fe08007e00, 0x3c8fe09c00e00, 0x3c8fe09c07000, 0x3c8fe09c07f00, 0x3c8ff49c07ff0, 0x3c8ff6bc07f30, 0x3c8ffcdc07fc0, 0x3c8ffefc07fff, 0x3cafe09c07f00, 0x3cafe2bc07f00, 0x3cb9011c78000, 0x3cbfe3bc7ff3f, 0x3d8fe09c07f00, 0x3d8fe8dc07f00, 0x3d99011f88000, 0x3d9fe9df8ffcf, 0x3dafeafc07f00, 0x3db9011c00000, 0x3db9011ff8000, 0x3dbb619c00000, 0x3dbb6bfc0000f, 0x3dbb6bfffffff, 0x3dbfe19c07f00, 0x3dbfe3bc07f00, 0x3dbfe9dc07f00, 0x3dbfebfc07f0f, 0x3ecfe09c07f00, 0x3ecff49c07f00, 0x3ecff49fffff0, 0x3ee9001c70000, 0x3eedd63c70e30, 0x3eefe09c77f00, 0x3eeff6bc07f00, 0x3eeff6bc77f30, 0x3ef9011ff8000, 0x3efdf7bffffff, 0x3fc9001f80000, 0x3fcf9c5f870c0, 0x3fcfe09f87f00, 0x3fcffcdc07f00, 0x3fcffcdf87fc0, 0x3fd9011ff8000, 0x3fdfbddffffff, 0x3feffefff7ff0, 0x3ff90103f0000, 0x3ff9011c70000, 0x3ff9011f80000, 0x3ff9011ff8000, 0x3ff9151ff80f0, 0x3ff9173ff8030, 0x3ff91d5ff80c0, 0x3ff91f7ff80ff, 0x3ff9411ff8000, 0x3ff9433ff8000, 0x3ff963bff8f3f, 0x3ffb011ff8000, 0x3ffb095ff8000, 0x3ffb29dfff1cf, 0x3ffb4b7ff8000, 0x3ffb619ff8000, 0x3ffb63bff8000, 0x3ffb69dff8000, 0x3ffb6bfff800f, 0x3ffd811ff8000, 0x3ffd951ff8000, 0x3ffd951fffff0, 0x3ffdc11ff8e00, 0x3ffdd73ff8000, 0x3ffdd73ff8e30, 0x3fff811fff000, 0x3fff9d5ff8000, 0x3fff9d5fff0c0, 0x3fffdf7fffef0, 0x3fffe19ffff00, 0x3fffebfffff0f, 0x3ffff7bffff30, 0x3ffffddffffc0, 0x3fffffe3f7eff, 0x3ffffffc77f3f, 0x3fffffff87fcf, 0x3ffffffff8e3f, 0x3fffffffff0cf, 0x3ffffffffffff]

def levT6 : List (List ℕ) :=
  [[],
  [],
  [],
  [0xe32407a, 0xe32b45d],
  [0x3f8d22507b, 0x3f8d22b861, 0x3f8d230848, 0x3f8d224073, 0x3f8d22507d, 0x3f8d21ec65, 0x3f8941ec2c, 0x348941ec12, 0x3f8d82507b, 0x410d22507b, 0x410d82407b, 0x3f8d224080, 0x3f8d229c7b, 0x3f8d22b07b, 0x3f8d228c5d, 0x3f8d22b898, 0x3f8d21844a, 0x3f8ae1842c, 0x348ae18412, 0x3f8dc2b861, 0x41cd22b861, 0x41cdc2b85d, 0x3f8d217450, 0x3f8d22b874, 0x3f8d22b879, 0x3f8b42405d, 0x3f8e829470, 0x428e824070, 0x428e82945d, 0x3f89017443, 0x380901c03f, 0x380a51743f, 0x388901743f, 0x3f8e324070, 0x3f8e32945d, 0x348b62405d, 0x434d22ac78, 0x434e524078, 0x434e52ac5d, 0x3489017440, 0x324901e03f, 0x324ab1743f, 0x38cd224078, 0x38cd22ac5d, 0x3f8d22cc3f, 0x3f8d2308af, 0x3f8d212036, 0x3f8c21202c, 0x348c212012, 0x3f8ea30848, 0x43cd230848, 0x43cea3083f, 0x3f8d21103f, 0x3f8a22403f, 0x3f8901443f, 0x3489c2403f, 0x3489015c3f, 0x3f8721743f, 0x3f8811743f, 0x348691743f, 0x348891743f, 0x314901e83f, 0x314ad1743f, 0x38c901743e, 0x2405d0fc31, 0x318901743f],
  [0xfe348901743f, 0xfe348b72405d, 0xfe3489a2403f, 0xfe348671743f, 0xfe2405d0fc2c, 0xd22405d0fc12, 0xfe348b726890, 0xfe348b719c5d, 0xfe2dc901742c, 0xd22dc9017412, 0xfe348901ec14, 0xfe348941743f, 0xfe360901743f, 0x104348901743f, 0xfe348ae17418, 0xfe348901843f, 0xfe370901743f, 0x107348901743f, 0xfe3a09017434, 0xe0348901743f, 0xfe348901c03f, 0xfe348a51743f, 0x10a348901743f, 0x10d348901743b, 0xfe324901743f, 0xfe348901e03f, 0xfe348ab1743f, 0xfe394901743f, 0xfe3489a19c3f, 0xfe268900fc2c, 0xd2268900fc12, 0xfe348c20fc21, 0xfe3489017448, 0xfe3a8901743f, 0x10f348901743f, 0xfe3c0901303f, 0x113348901543f, 0xfe19c5d0fc2c, 0xd219c5d0fc12, 0xfe3dc7f1743f, 0x116348881743f, 0x901743f0b012, 0x118314901743f, 0xfe348b726867, 0xfe2dc9a2402c, 0xd22dc9a24012, 0xfe348c22dc21, 0xfe3a8b72405d, 0x10f348b72405d, 0xfe348ba24052, 0xfe3c0b72404c, 0x113348b724055, 0xfe2dc671742c, 0xd22dc6717412, 0xfe348bd2145d, 0xfe3dcb71fc5d, 0x116348b72205d, 0xfe3acb02405d, 0x110348b52405d, 0xb72405d0b012, 0x118314b72405d, 0xfe348b72505d, 0xfe360b72405d, 0x104348b72405d, 0xfe348b724061, 0xfe370b72405d, 0x107348b72405d, 0xe0348b72405d, 0xfe348b724070, 0xfe348b72945d, 0x10a348b72405d, 0xfe324b72405d, 0xfe348b724078, 0xfe348b72ac5d, 0xfe394b72405d, 0xfe3e4d22407b, 0x3f8d22507b, 0xfe348941ec14, 0xfe348942407b, 0xfe360901ec14, 0x104348901ec14, 0xfe348901f414, 0xfe3487b19c14, 0xfe2407b0b014, 0xd22407b05012, 0xfe348941ec3f, 0xfe360901ec3f, 0x104348901ec3f, 0xfe348941ec5d, 0xfe348c22b87b, 0xfe348901ec25, 0xfe348ae17428, 0xfe348901ec1b, 0xfe348c20fc28, 0xfe348901ec37, 0xfe3c0901903f, 0xfe348901ec3c, 0x113348901d43f, 0xfe33c901743f, 0xfb348901743f, 0xfe3d8901743f, 0x115348901743f, 0xfe3488e1743f, 0xfc348901743f, 0xfe3488f1743f, 0xfe340901743f, 0x3f8e3348901ec5d, 0xfe338901743f, 0xf8348901743f, 0xfe3489a2503f, 0xfe348651743f, 0xfe2505d0fc2c, 0xd22505d0fc12, 0xfe360941743f, 0x104348941743f, 0xfe3609a2403f, 0xfe360671743f, 0xfe2405d0fc29, 0xd82405d0fc12, 0x104360901743f, 0xfe348911743f, 0x103348901743f, 0x1043489a2403f, 0x104348671743f, 0x1042405d0fc2c, 0xd22405d0fc0f, 0xfe348931743f, 0xfe35c901743f, 0xfe2405d0fc2d, 0xd22405d0fc15, 0xfe3c8d22b85d, 0x3f8d22b861, 0xfe348ae18418, 0xfe348ae1845d, 0xfe370ae17418, 0x107348ae17418, 0xfe348ae26818, 0xfe3485d12818, 0xfe2b85d0b018, 0xd22b85d06012, 0xfe348ae1843f, 0xfe370ae1743f, 0x107348ae1743f, 0xfe348ae24061, 0xfe348ae1741b, 0xfe348c20fc25, 0xfe3bc901743f, 0x112348901743f, 0xfe348ae17439, 0xfe3dc971743f, 0xfe348ae1743d, 0x116348a81743f, 0xfe3489016c3f, 0xfd348901743f, 0xfe348901703f, 0xfe344901743f, 0x3f8e3348ae2405d, 0xfe330901743f, 0xf1348901743f, 0xfe348982403f, 0xfe348671843f, 0xfe240610fc2c, 0xd2240610fc12, 0xfe370901843f, 0x107348901843f, 0xfe3709a2403f, 0xfe370671743f, 0xfe2405d0fc26, 0xdc2405d0fc12, 0x107370901743f, 0xfe348901783f, 0x106348901743f, 0x1073489a2403f, 0x107348671743f, 0x1072405d0fc2c, 0xd22405d0fc0d, 0xfe348901803f, 0xfe36c901743f, 0xfe2405d0fc2e, 0xd22405d0fc19, 0xfe3a0c42405d, 0xfe3a0901c034, 0xfe3a0a517434, 0x10a3a09017434, 0xfe3a09a24034, 0xfe3a06717434, 0xfe2405d0d01f, 0xe83809017434, 0xe82405d0d012, 0xfe3a0901c03f, 0xfe3a0a51743f, 0x10a3a0901743f, 0xe02405d0fc34, 0xe03489a2403f, 0xfe3a09017437, 0xfe3c0901383f, 0xf0380901743f, 0xe0348671743f, 0xfe3a09017439, 0xfe3dc831743f, 0xf7380901743f, 0xe02405d0fc2c, 0xfe3a0901743e, 0x118380901743f, 0xff348901743f, 0xe5380901743f, 0xd22405d0fc23, 0xd22405d0fc11, 0xfe348901643f, 0xfe3488c1743f, 0xd230c901743f, 0xfe348902103f, 0xfe3487019c3f, 0xfe240700fc2c, 0xfe314901c03f, 0xd2240700fc12, 0xfe348a51c03f, 0x10a348901c03f, 0xfe348a52683f, 0xfe3485d13c3f, 0xfe2945d0fc2c, 0xfe314a51743f, 0xd22945d0fc12, 0x10a348a51743f, 0x10a3489a2403f, 0x10a348671743f, 0x10a2405d0fc2c, 0x10a324901743f, 0xd22405d0fc0b, 0x10a314901743f, 0xfe348901bc3f, 0xfe348a41743f, 0xfe3489b2403f, 0xfe348681743f, 0xfe38c9017434, 0xd22405d0fc35, 0x10d348b82405d, 0x10d348901e03b, 0x10d348ab1743b, 0x10d394901743b, 0x10d3489a2403b, 0x10d348671743b, 0x10d2405d0ec2c, 0x10d324901743b, 0xd22405d0ec0a, 0x10d348901e03f, 0x10d348ab1743f, 0x10d394901743f, 0xc92405d0fc3b, 0xfe3249a2403f, 0x10d348901743c, 0x113348901583f, 0x113324901743f, 0xfe324671743f, 0x10d348901743d, 0x1163488a1743f, 0x116324901743f, 0xfe2405d0fc2b, 0x10d348901743e, 0x118324901743f, 0xfe2405d0fc30, 0xc92405d0fc12, 0xfe34c901743f, 0xfe348901503f, 0xfe348871743f, 0xfe2c8901743f, 0xfe348901f83f, 0xfe3487819c3f, 0xfe240780fc2c, 0xd2314901e03f, 0xd2240780fc12, 0xfe348ab1e03f, 0xfe394901e03f, 0xfe348ab2683f, 0xfe3485d12c3f, 0xfe2ac5d0fc2c, 0xd2314ab1743f, 0xd22ac5d0fc12, 0xfe394ab1743f, 0xfe3949a2403f, 0xfe394671743f, 0xfe2405d0fc20, 0xe52405d0fc12, 0xe5314901743f, 0xfe3489e2403f, 0xfe3486b1743f, 0xfe2405d1143f, 0xe3348901743b, 0xfe348a02403a, 0xfe268670fc2c, 0xd2268670fc12, 0xfe348a62083f, 0xfe3dc9a1fc3f, 0x1163489a2203f, 0xfe378962403f, 0xdd3489a2403f, 0x108348992403f, 0xfe3209a2403f, 0x9a2403f0b012, 0x1183149a2403f, 0xfe3489a24048, 0xfe3a89a2403f, 0x10f3489a2403f, 0xdd348901743f, 0xfe320901743f, 0xfe37c901743f, 0x109348901743f, 0xfe390d23083f, 0x3f8d230848, 0xfe348c212021, 0xfe348c21203f, 0xfe3a8c20fc21, 0x10f348c20fc21, 0xfe3483f0d821, 0xfe3083f0b021, 0xd23083f08412, 0xfe348c217448, 0xfe348c224048, 0x460c5308901743f, 0xfe328901743f, 0xe1348901743f, 0xfe348af2405d, 0xfe3486717448, 0xfe2405d1202c, 0xd22405d12012, 0xfe3a89017448, 0x10f3489017448, 0xfe3a8671743f, 0xfe2405d0fc1d, 0xea2405d0fc12, 0x10f3a8901743f, 0xfe3489017441, 0x10e348901743f, 0x10f348671743f, 0x10f2405d0fc2c, 0xd22405d0fc08, 0xfe3489017446, 0xfe3a4901743f, 0xfe2405d0fc2f, 0xd22405d0fc22, 0xfe348a71743f, 0x10b348901743f, 0xfe3c0901b83f, 0xfe3c0a92403f, 0xfe3c0671303f, 0xfe2404c0fc1a, 0xf02404c0fc12, 0xfe3c09014c3f, 0xfe3dc861743f, 0x11a314901743f, 0xfe348901b05d, 0xfe348bc1743f, 0xfe348ac1743f, 0xfe398901743f, 0x113348901dc3f, 0x1133489d2403f, 0x113348671543f, 0x113240550fc2c, 0xd2240550fc06, 0x113348901603f, 0x1163488b1743f, 0xfe3486d17438, 0xfe348711343f, 0xfe368631743f, 0xd9348671743f, 0x105348661743f, 0xfe31c671743f, 0x671743f0b012, 0x118314671743f, 0xd9348901743f, 0xfe31c901743f, 0xfe348901d03f, 0x10c348901743f, 0xfe3dca11743f, 0xfe3dc761743f, 0xfe1fc5d0fc16, 0xf71fc5d0fc12, 0x11b314901743f, 0xfe3489f2405d, 0xfe348b92403f, 0xfe348901e43f, 0xfe39c901743f, 0x116348aa1743f, 0x1163486a1743f, 0x1162205d0fc2c, 0xd22205d0fc04, 0xfe2405d11c1c, 0xfe240620fc24, 0x1002405d0fc2c, 0xfe2545d0fc27, 0x1012405d0fc2c, 0x1022405d0fc2a, 0x100348901743f, 0x101348901743f, 0xfe348901e83f, 0xfe348ad1743f, 0xc52405d0fc3e, 0x11838c901743f, 0x1182405d0fc32, 0xc52405d0fc02, 0xd22405d10807, 0xd22405f0fc0c, 0xd42405d0fc12, 0xd22485d0fc0e, 0xd52405d0fc12, 0xd62405d0fc10, 0xfe350901743f, 0xfe354901743f],
  [0xfe348901743f, 0x3f8d22405d0fc3f, 0xfe348b72405d, 0x3f8d22dc901743f, 0x3f8d22407b1743f, 0x3f8d22405d0fc14, 0x3f8d22b8901743f, 0x3f8d22405d0fc18, 0x3f8e8348901743f, 0x3f8d22405d0fc34, 0x434fe348901743f, 0x3f8d22405d0fc3b, 0x3f8d22405d1743f, 0xfe3489a2403f, 0x3f8d2268901743f, 0x3f8d2308901743f, 0x3f8d22405d0fc21, 0x3f8f0348901743f, 0x3f8d22405d1303f, 0x44cfe348901743f, 0x3f8d22405d1543f, 0x3f8d2240901743f, 0xfe348671743f, 0x3f8d2240671743f, 0x3f8f7348901743f, 0x3f8d22407f1743f, 0x458fe348901743f, 0x3f8d2240881743f, 0x3f8d2348901743f, 0xfe2405d0fc2c, 0x3f8d22405d0fc2c, 0x460fe348901743f, 0x3f8d2314901743f, 0x3f8fe348901743f, 0xd22405d0fc12, 0x3f8d22405d0fc12, 0x3f8d2268900fc3f, 0x3f8d219c5d0fc3f, 0x3f8901743f0fc2c, 0x348901743f0fc12, 0x3f8d22dc901745d, 0xfe348b726890, 0x3f8d22dc9a2405d, 0x3f8d2308b72405d, 0x3f8d22dc9017421, 0x3f8d22e8b72405d, 0x3f8d22dc9017452, 0x3f8f0348b72405d, 0x3f8d22dc901744c, 0x44cfe348b72405d, 0x3f8d22dc9017455, 0x3f8d22dc902405d, 0xfe348b719c5d, 0x3f8d22dc9019c5d, 0x3f8d22f4b72405d, 0x3f8d22dc902145d, 0x3f8f7348b72405d, 0x3f8d22dc901fc5d, 0x458fe348b72405d, 0x3f8d22dc902205d, 0x3f8d22dcb72405d, 0x3f8eb348b72405d, 0x3f8d22dcb02405d, 0x440fe348b72405d, 0x3f8d22dcb52405d, 0x3f8d2348b72405d, 0xfe2dc901742c, 0x3f8d22dc901742c, 0x460fe348b72405d, 0x3f8d2314b72405d, 0x3f8fe348b72405d, 0xd22dc9017412, 0x3f8d22dc9017412, 0x3f8d22dc901ec5d, 0x3f8d22dc9017414, 0x3f8d22dcae2405d, 0x3f8d22dc9017418, 0x484fe348901743f, 0x484fe348b72405d, 0x3f8d22405d0fc01, 0x3f8d22dc9017401, 0x3f8e8348b72405d, 0x3f8d22dc9017434, 0x434fe348b72405d, 0x3f8d22dc901743b, 0x3f8d22dc9a2403f, 0x3f8d22e8901743f, 0x3f8d22405d1483f, 0x3f8d22dc671743f, 0x3f8d22f4901743f, 0x3f8d2240851743f, 0x3f8eb348901743f, 0x3f8d22c0901743f, 0x440fe348901743f, 0x3f8d22d4901743f, 0x3f8b72405d0fc2c, 0x348b72405d0fc12, 0xfe348901ec14, 0x3f8d22407b0fc14, 0x3f8d22407b17414, 0x3f8d22b8901ec5d, 0x3f8d2268901ec3f, 0x3f8d2308901ec3f, 0x3f8f0348901ec3f, 0x44cfe348901ec3f, 0x3f8d22407d1743f, 0x470fe348901743f, 0x3f8d22405d0fc28, 0x474fe348901743f, 0x3f8d2240641743f, 0x47cfe348901743f, 0x3f8d2240751743f, 0x3f8d21ec671743f, 0x3f8901ec5d0fc2c, 0xfe348c52407b1743f, 0x348901ec5d0fc12, 0x3f8f9348901743f, 0xfe348941743f, 0x3f8d22505d0fc14, 0x3f8d2250901743f, 0xfe360901743f, 0x3f8d82405d0fc14, 0x3f8d8348901743f, 0x3f8d22405d0fc03, 0x104348901743f, 0x410d22405d0fc14, 0x410fe348901743f, 0x3f8d22405d0fc13, 0x3f8d2268900fc14, 0x3f8d219c5d0fc14, 0x3f8901743f0b014, 0x348901743f05012, 0xfe348ae17418, 0x3f8d22b85d0fc18, 0x3f8d22b89017418, 0x3f8d22b89a2403f, 0x3f8d2308ae1743f, 0x3f8d22405d0fc25, 0x3f8d22b8671743f, 0x3f8f7348ae1743f, 0x458fe348ae1743f, 0x3f8d22405d1283f, 0x478fe348901743f, 0x3f8d225c901743f, 0x480fe348901743f, 0x3f8d22a0901743f, 0x3f8ae2405d0fc2c, 0xfe348c52b8901743f, 0x348ae2405d0fc12, 0x3f8f2348901743f, 0xfe348901843f, 0x3f8d2240610fc18, 0x3f8d2240611743f, 0xfe370901743f, 0x3f8dc2405d0fc18, 0x3f8dc348901743f, 0x3f8d22405d0fc05, 0x107348901743f, 0x41cd22405d0fc18, 0x41cfe348901743f, 0x3f8d22405d0fc17, 0x3f8d2268900fc18, 0x3f8d219c5d0fc18, 0x3f8901743f0b018, 0x348901743f06012, 0xfe3a09017434, 0x3f8e82405d0fc34, 0x3f8e83489017434, 0x3f8e83489a2403f, 0x3f8f03a0901743f, 0x3f8d22405d1383f, 0x3f8e8348671743f, 0x3f8f73a0901743f, 0x3f8d2240831743f, 0x3f8e82405d0fc2c, 0x460fe3a0901743f, 0x3f8d22405d0fc1f, 0x464fe348901743f, 0xe0348901743f, 0x3a0e0348901743f, 0x3f8e0348901743f, 0x3a0d22405d0fc12, 0x3f8d2310901743f, 0xfe348901c03f, 0x3f8d2240700fc34, 0x3f8d2240701743f, 0xfe348a51743f, 0x3f8d22945d0fc34, 0x3f8d2294901743f, 0x10a348901743f, 0x428d22405d0fc34, 0x428fe348901743f, 0x3f8d22405d0fc33, 0x3f8d2268900fc34, 0x3f8d219c5d0fc34, 0x3f8901743f0d02c, 0x3f8c52405d0fc34, 0x348901743f0d012, 0x10d348901743b, 0x434d22405d0fc3b, 0x434fe348901743b, 0x434fe3489a2403f, 0x44d0d348901743f, 0x3f8d22405d1583f, 0x434fe348671743f, 0x4590d348901743f, 0x3f8d22408a1743f, 0x434fe2405d0fc2c, 0x4610d348901743f, 0xfe324901743f, 0x3f8d2324901743f, 0x434fe324901743f, 0x434d22405d0fc12, 0x3f8d22405d0fc0a, 0x3f8d22e0901743f, 0xfe348901e03f, 0x3f8d2240780fc3b, 0x3f8d2240781743f, 0xfe348ab1743f, 0x3f8d22ac5d0fc3b, 0x3f8d22ac901743f, 0xfe394901743f, 0x3f8e52405d0fc3b, 0x3f8e5348901743f, 0x3f8d2268900fc3b, 0x3f8d219c5d0fc3b, 0x3f8901743f0ec2c, 0x348c52405d0fc3b, 0x348901743f0ec12, 0x3f8d219c5d1743f, 0x3f8901745d0fc2c, 0x348901745d0fc12, 0x3f8d22809a2403f, 0x3f8d2268900fc3a, 0x3f8d2268902403f, 0xfe3489a19c3f, 0x3f8d22689019c3f, 0x3f8d22989a2403f, 0x3f8d2268902083f, 0x3f8f73489a2403f, 0x3f8d2268901fc3f, 0x458fe3489a2403f, 0x3f8d2268902203f, 0x3f8d22689a2403f, 0x3f8de3489a2403f, 0x3f8d2268962403f, 0x420fe3489a2403f, 0x3f8d2268992403f, 0x3f8d23489a2403f, 0xfe268900fc2c, 0x3f8d2268900fc2c, 0x460fe3489a2403f, 0x3f8d23149a2403f, 0x3f8fe3489a2403f, 0xd2268900fc12, 0x3f8d2268900fc12, 0x3f8d2280901743f, 0x3f8d22405d0fc3a, 0x3f8d23089a2403f, 0x3f8d2268900fc21, 0x484fe3489a2403f, 0x3f8d2268900fc01, 0x3f8f03489a2403f, 0x3f8d2268901303f, 0x44cfe3489a2403f, 0x3f8d2268901543f, 0x3f8d2268671743f, 0x3f8d2298901743f, 0x3f8d2240821743f, 0x3f8de348901743f, 0x3f8d2258901743f, 0x420fe348901743f, 0x3f8d2264901743f, 0x3f89a2405d0fc2c, 0x3489a2405d0fc12, 0x3f8d22405d0fc1b, 0xfe348c20fc21, 0x3f8d23085d0fc21, 0x3f8d2308900fc21, 0x3f8d2308671743f, 0x3f8d22405d0fc36, 0x3f8fa348901743f, 0x3f8d22c4901743f, 0x45cfe348901743f, 0x3f8d22fc901743f, 0x3f8c22405d0fc2c, 0x1183f8d2308901743f, 0xfe348c5308901743f, 0x348c22405d0fc12, 0x3f8e4348901743f, 0xfe3489017448, 0x3f8d22405d12021, 0x3f8d22405d1203f, 0xfe3a8901743f, 0x3f8ea2405d0fc21, 0x3f8ea348901743f, 0x3f8d22405d0fc09, 0x10f348901743f, 0x43cd22405d0fc21, 0x43cfe348901743f, 0x3f8d22405d0fc1e, 0x3f8d219c5d0fc21, 0x3f8901743f0b021, 0x348901743f08412, 0x3f8d22405d0fc37, 0xfe3c0901303f, 0x3f8f02405d1303f, 0x3f8f0348901303f, 0x3f8f0348671743f, 0x3f8f73c0901743f, 0x3f8d2240861743f, 0x3f8f02405d0fc2c, 0x3f8f0314901743f, 0x3f8d22405d0fc1a, 0x468fe348901743f, 0x3f8ec348901743f, 0x3c0d22405d0fc12, 0x3f8d22406e1743f, 0x3f8d22a4901743f, 0x3f8d22f8901743f, 0x444fe348901743f, 0x3f8d22405d1243f, 0x3f8d219c5d1303f, 0x3f8901744c0fc2c, 0x348901744c0fc12, 0x3f8d22405d0fc3c, 0x113348901543f, 0x44cd22405d1543f, 0x44cfe348901543f, 0x44cfe348671743f, 0x45913348901743f, 0x3f8d22408b1743f, 0x44cfe2405d0fc2c, 0x44cd2314901743f, 0x3f8d232c901743f, 0x44cd22405d0fc12, 0x3f8d22405d0fc06, 0x3f8d2240771743f, 0x3f8d2274901743f, 0x3f8d2304901743f, 0x3f8ee348901743f, 0x3f8d219c5d1543f, 0x3f890174550fc2c, 0x34890174550fc12, 0x3f8902405d0fc2c, 0x348902405d0fc12, 0x3f8d21b4671743f, 0x3f8d219c5d0fc38, 0x3f8d21c4671743f, 0x3f8d219c5d1343f, 0x3f8d219c671743f, 0x3f8da348671743f, 0x3f8d219c631743f, 0x414fe348671743f, 0x3f8d219c661743f, 0x3f8d2348671743f, 0xfe19c5d0fc2c, 0x3f8d219c5d0fc2c, 0x460fe348671743f, 0x3f8d2314671743f, 0x3f8fe348671743f, 0xd219c5d0fc12, 0x3f8d219c5d0fc12, 0x3f8d22406d1743f, 0x3f8d22405d0fc38, 0x3f8d2240711743f, 0x3f8d22405d1343f, 0x484fe348671743f, 0x3f8d219c5d0fc01, 0x3f8da348901743f, 0x3f8d2240631743f, 0x414fe348901743f, 0x3f8d2240661743f, 0x3f8f7348671743f, 0x3f8d21fc671743f, 0x458fe348671743f, 0x3f8d2220671743f, 0x3f89019c5d0fc2c, 0x3489019c5d0fc12, 0x3f8d22405d0fc39, 0x3f8d22405d14c3f, 0xfe3dc7f1743f, 0x3f8f72407f1743f, 0x3f8f73487f1743f, 0x3f8f72405d0fc2c, 0x3f8f7314901743f, 0x3f8d22405d0fc16, 0x46cfe348901743f, 0x3f8f3348901743f, 0x3dcd22405d0fc12, 0x3f8d2284901743f, 0x3f8d22ec901743f, 0x3f8d2240761743f, 0x450fe348901743f, 0x3f8d22407c1743f, 0x3f8901fc5d0fc2c, 0x348901fc5d0fc12, 0x3f8d22405d0fc3d, 0x3f8d22405d1603f, 0x116348881743f, 0x458d2240881743f, 0x458fe348881743f, 0x458fe2405d0fc2c, 0x458d2314901743f, 0x3f8d2334901743f, 0x458d22405d0fc12, 0x3f8d22405d0fc04, 0x3f8d22a8901743f, 0x3f8d2300901743f, 0x3f8d22406a1743f, 0x3f8f5348901743f, 0x3f8902205d0fc2c, 0x348902205d0fc12, 0x348d22405d0fc12, 0x3f8901743f0b02c, 0x3f890174470fc2c, 0x3f8901743f0b01c, 0x3f8901885d0fc2c, 0x3f8901743f0b024, 0x3f8952405d0fc2c, 0x3f8901743f0b027, 0x408fe2405d0fc2c, 0x3f8901743f0b02a, 0x3f8fe2405d0fc2c, 0x901743f0b012, 0x3f8901743f0b012, 0x3f8d22405d11c3f, 0x3f8d22405d0fc1c, 0x3f8d2240621743f, 0x3f8d22405d0fc24, 0x3f8d2254901743f, 0x3f8d22405d0fc27, 0x484fe2405d0fc2c, 0x3f8901743f0b001, 0x408fe348901743f, 0x3f8d22405d0fc2a, 0x460fe2405d0fc2c, 0x3f8c52405d0fc2c, 0x348901743f0b012, 0x3f8d22405d0fc3e, 0x3f8d22405d1683f, 0x3f8d22408d1743f, 0x118314901743f, 0x460d2314901743f, 0x460fe314901743f, 0x460d22405d0fc12, 0x3f8d22405d0fc02, 0x3f8e3348901743f, 0x3f8ed348901743f, 0x3f8f4348901743f, 0x3f8d22405d0fc32, 0x348c52405d0fc12, 0x348901743f04812, 0x34890174420fc12, 0x348901743f04807, 0x3489017c5d0fc12, 0x348901743f0480c, 0x348922405d0fc12, 0x348901743f0480e, 0x358d22405d0fc12, 0x348901743f04810, 0x3f8d22405d1083f, 0x3f8d22405d0fc07, 0x3f8d22405f1743f, 0x3f8d22405d0fc0c, 0x3f8d2248901743f, 0x3f8d22405d0fc0e, 0x3f8d6348901743f, 0x3f8d22405d0fc10, 0x484d22405d0fc12, 0x348901743f04801],
  [0xfe348901743f, 0x3f8d22405d0fc3f, 0xfe348b72405d, 0x3f8d22dc901743f, 0x3f8d22407b1743f, 0x3f8d22405d0fc14, 0x3f8d22b8901743f, 0x3f8d22405d0fc18, 0x3f8e8348901743f, 0x3f8d22405d0fc34, 0x434fe348901743f, 0x3f8d22405d0fc3b, 0x3f8d22405d1743f, 0xfe3489a2403f, 0x3f8d2268901743f, 0x3f8d2308901743f, 0x3f8d22405d0fc21, 0x3f8f0348901743f, 0x3f8d22405d1303f, 0x44cfe348901743f, 0x3f8d22405d1543f, 0x3f8d2240901743f, 0xfe348671743f, 0x3f8d2240671743f, 0x3f8f7348901743f, 0x3f8d22407f1743f, 0x458fe348901743f, 0x3f8d2240881743f, 0x3f8d2348901743f, 0xfe2405d0fc2c, 0x3f8d22405d0fc2c, 0x460fe348901743f, 0x3f8d2314901743f, 0x3f8fe348901743f, 0xd22405d0fc12, 0x3f8d22405d0fc12],
  [0xfe348901743f]]

def actT6 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x882001102002200, 0x882001102002200],
  [0x20c1804182008302010600, 0x1dc1803b8200770200ee00, 0x8c1801182002302004600, 0x0, 0x10602, 0x10602, 0x10602, 0x10602, 0x21c1804382008702010e00, 0x504180a082014102028200, 0x544180a88201510202a200, 0x0, 0x11a7502341804682008d02011a00, 0x10676020c1804182008302010600, 0x0, 0xee02, 0xee02, 0xee02, 0xee02, 0x1dc1803b8200770200ee00, 0x1dc1803b8200770200ee00, 0x1dc1803b8200770200ee00, 0x0, 0x13a7502741804e82009d02013a00, 0xee7601dc1803b8200770200ee00, 0x0, 0xf27601e41803c8200790200f200, 0xf27601e41803c8200790200f200, 0xf27601e41803c8200790200f200, 0x0, 0x226100441800882001102002200, 0x226100441800882001102002200, 0x441800882001102002200, 0x89d80113502de6200441800882001102002200, 0x89d80113502de6200441800882001102002200, 0x0, 0xf67501ec1803d82007b0200f600, 0xf67501ec1803d82007b0200f600, 0xf67501ec1803d82007b0200f600, 0x0, 0x226100441800882001102002200, 0x226100441800882001102002200, 0x89d40112902ee4a00441800882001102002200, 0x89d40112902ee4a00441800882001102002200, 0x0, 0x4602, 0x4602, 0x4602, 0x4602, 0x8c1801182002302004600, 0x8c1801182002302004600, 0x5e4180bc8201790202f200, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x9880113080006000441800882001102002200, 0x9880113080206000441800882001102002200, 0x44ca008988011250022490040900088e801f1c80003800441800882001102002200, 0x0, 0x0],
  [0x221000441800882001102002200, 0x220a, 0x220a, 0x220a, 0x2202, 0x2202, 0x0, 0x0, 0x0, 0x0, 0x22504043988081250106490000900418f40831d010610020c1804182008302010600, 0x94740378e40001c002a1000541800a82001502002a00, 0x1331d00ea1001d41803a8200750200ea00, 0x1351d002a1000541800a82001502002a00, 0x1dd0403b9880772680ee4a01dc7404a8e40101c00ee1001dc1803b8200770200ee00, 0xf49403b9240102400321000641800c82001902003200, 0x1372500e21001c4180388200710200e200, 0x1392500321000641800c82001902003200, 0x3ca780794100f26501e4c403c9280791d00f21001e41803c8200790200f200, 0x22990044e400f9a80113300221000441800882001102002200, 0x8a7401b3100221000441800882001102002200, 0x8a7401b3100221000441800882001102002200, 0x8a7401b3100221000441800882001102002200, 0x3da7407b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x229a00452400fa280114300221000441800882001102002200, 0x8a7801d4100221000441800882001102002200, 0x8a7801d4100221000441800882001102002200, 0x8a7801d4100221000441800882001102002200, 0x0, 0x0, 0x0, 0x8d040119880232680464a008c740038e40201c004610008c1801182002302004600, 0x1f4a401194402028004610008c1801182002302004600, 0xe21001c4180388200710200e200, 0xe61001cc180398200730200e600, 0x44da0089a80e31d00221000441800882001102002200, 0x451a008a280f91d00221000441800882001102002200, 0x0, 0x0, 0x44ea0089c81112500221000441800882001102002200, 0x452a008a481232500221000441800882001102002200, 0x0, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x0, 0x0, 0x0, 0x4606, 0xe20a, 0xe60a, 0x0, 0x220a, 0x220a, 0x0, 0x0, 0x0, 0x220a, 0x220a, 0x0, 0x0, 0x0, 0x220a, 0x2a0a, 0xea0a, 0x2a0a, 0x320a, 0xe20a, 0x320a, 0x220a, 0x220a, 0x220a, 0x220a, 0x220a, 0x220a, 0x220a, 0x220a, 0x303201060e, 0x20cee0419cc08337827a6b020cce04198c0832b827e53020c9e04192c13b1f81063b020c1e0380380830680000c022c1603002808304800008020c0e02801813d02800004020c0602000808300800000, 0x834281028205050204820008332810262021cc20401800812681024a04f4920001200811e81023a020c720000e00810801020c02041004081008301010200, 0x1068d020d120419b408334810655020ca409e9440002801064e020c7c0418e80830801060c020c1004181808302010600, 0x40a0808740814080021cca04398808125010e490200900438f40871d010e10021c1804382008702010e00, 0x44a1408941010262021cc2050180081250112490240900448f40891d01121002241804482008902011200, 0x201200b01c010606, 0x10606, 0x6030010606, 0x7034010602, 0x20d0a046a0408d3281066104ec9a0129240251e804a3a020c720000e002508004a0c00941001281008301004a00, 0x8d4082866504cc920998f41331d02661004cc1809982013302026600, 0x894281066104d49209a8f41351d026a1004d41809a82013502026a00, 0x20d0a037a040833280de6102049a03792406f1e80de3a020c720000e006f0800de0c01bc100378101450100de00, 0x51d220a39c40252b00de550000a800993809f2680204c004c7c06c8f40201e002610004c1800982001302002600, 0x22504043988081250106490000900418f40831d010610020c1804182008302010600, 0x1dd0403b9880772680ee4a01dc7404a8e40101c00ee1001dc1803b8200770200ee00, 0x2250404398813b250106490000900418f40831d010610020c1804182008302010600, 0x8d040119880232680464a008c740038e40201c004610008c1801182002302004600, 0x11a9d0435040a198814925011a490300900468f408d1d011a1002341804682008d02011a00, 0x44da0089a80e31d00221000441800882001102002200, 0x1069e022504043988081250106490340900418f40831d010610020c1804182008302010600, 0x451a008a280f91d00221000441800882001102002200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x389d41372500e21001c4180388200710200e200, 0x39a541392500e61001cc180398200730200e600, 0x713900e21001c4180388200710200e200, 0x113900221000441800882001102002200, 0x734900e61001cc180398200730200e600, 0x114900221000441800882001102002200, 0xa7b000115a029aa8004518041a1001136029660, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2a0a, 0x501c002a0a, 0x6028002a02, 0x7028002a02, 0x94740438e40801c002a1000541800a82001502002a00, 0x94740a08e40901c002a1000541800a82001502002a00, 0xea0a, 0xea0a, 0xea02, 0xea02, 0x94740a88e40a01c002a1000541800a82001502002a00, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2a0a, 0x2a0a, 0x2a02, 0x2a02, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2202, 0x2202, 0xe03600ee0e, 0x1dcee03b9cc0773780ee6b01dcce04a98c0772b80ee5301dc9e04c92c1531f80ee3b01dc1e0900380770680200c026c160880280770480200801dc0e0800180770280200401dc0607800809500802000, 0x774280ee8201dd020a02000773280ee6201dcc20981800772680ee4a01dc920081200771e80ee3a0254720080e00770800ee0c01dc1003b8100770100ee00, 0xee8505550203b99409930812e55025c9a03b9240951e812a3a0254720080e009508012a0c02541004a81007701012a00, 0x3ba080774082a08001dcca03b9880772680ee4a01dc7404a8e41301c00ee1001dc1803b8200770200ee00, 0x3ba140774100ee6201dcc20a81800772680ee4a01dc7404a8e41401c00ee1001dc1803b8200770200ee00, 0xee06, 0x801201601c00ee06, 0x1102400ee06, 0x1202800ee02, 0x1dd0a04ea0409d3280ee6100f49a01e92807724802048054c7a0098e403d08007a0c00f41001e81007701007a00, 0x9d40813a6504dc9a09b9281571c826e1004dc1809b82013702026e00, 0x774280ee6104e49a09c9281591c82721004e41809c82013902027200, 0x1dd1a03ba240773680ee6901dcaa03b9480772880205001dc7c04f8e80770800ee0c01dc100118180770200ee00, 0x575040ad98809726812e4a054c7404a8e40101c012e10025c1804b82009702012e00, 0x3550406a9880d52681aa4a0354740038e40201c01aa1003541806a8200d50201aa00, 0x3a9b41331d00ea1001d41803a8200750200ea00, 0x3fa341351d00fe1001fc1803f82007f0200fe00, 0x13a9d02750404e98809d26813a4a0274740af8e41701c013a1002741804e82009d02013a00, 0x44ea0089c81112500221000441800882001102002200, 0xee9e01dd0403b9880772680ee4a01dc7404a8e41801c00ee1001dc1803b8200770200ee00, 0x452a008a481232500221000441800882001102002200, 0x753500d61001ac1803582006b0200d600, 0x1f3500221000441800882001102002200, 0x7f4500da1001b41803682006d0200da00, 0x1f4500221000441800882001102002200, 0xb2b000115e02c6b000452803ba300113a02c268, 0x221000441800882001102002200, 0x221000441800882001102002200, 0xf01c00320a, 0x320a, 0x11034003202, 0x12034003202, 0xf49403b9241302400321000641800c82001902003200, 0xf49403b9241402400321000641800c82001902003200, 0xe20a, 0xe20a, 0xe202, 0xe202, 0xf49403b9241502400321000641800c82001902003200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x320a, 0x320a, 0x3202, 0x3202, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2202, 0x2202, 0x1903a00f20a, 0x1e53c03ca080794083608001e4ca03c9880792500f24906809003c8f40791d00f21001e41803c8200790200f200, 0x1e53c03ca080794083808001e4ca03c9880792680f24a01e4740548e41a01c00f21001e41803c8200790200f200, 0x1e53c03ca140794100f26501e4c403c9280792483804801e4740548e41b01c00f21001e41803c8200790200f200, 0xf20a, 0xf20a, 0x1d01c00f202, 0x1e53a03ca680794280f28201e4c403c9280791d00f21001e41803c8200790200f200, 0xf202, 0x369e00453a0f027001b40803665006cc40579240ad1e803610006c1800d82001b02003600, 0x369e00453a0f827001b40803665006cc403c9340791c803610006c1800d82001b02003600, 0x369e00453a10027007942803665006cc40579240791c803610006c1800d82001b02003600, 0x2289004504008a04200400022620044c20f818001125003e490780900088f40111d00221000441800882001102002200, 0x220a, 0x56a7816741015a6502b4c40b39280ad1d015a1002b4180568200ad02015a00, 0x2d4da05a9a80e31d016a1002d41805a8200b502016a00, 0xfa6816b49003e8d007d140b4a180091d003e10007c1800f82001f02003e00, 0x220a, 0x3ca780794100f26501e4c403c9280791d00f21001e41803c8200790200f200, 0x2e4ea05c9c81112501721002e41805c8200b902017200, 0x8a680114a80229205ad1402ba1800d2500221000441800882001102002200, 0x2202, 0x3ca780794100f26501e4c403c9280791d00f21001e41803c8200790200f200, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x221000441800882001102002200, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x2202, 0x2202, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x229d004534008a4801f450022860004c40089842103000221000441800882001102002200, 0x2202, 0x229d006cc403c9841a03000221000441800882001102002200, 0x229d006cc403c9841b03000221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x229d004534008a4801f450022860004c40089842203000221000441800882001102002200, 0x2202, 0x229d006cc403c9841c03000221000441800882001102002200, 0x220a, 0x220a, 0x2202, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x2202, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x220a, 0x220a, 0x229e0045240b7a28011410022650044c4008928011248440480044740b68e42101c00221000441800882001102002200, 0x2202, 0x2304a00f60a, 0x1ed3a03da1407b4100f66201ecc212818007b2500f64909009003d8f407b1d00f61001ec1803d82007b0200f600, 0x1ed3a03da1407b4100f66201ecc213018007b2680f64a01ec7405f8e42401c00f61001ec1803d82007b0200f600, 0x1ed3a03da1407b4100f66501ecc403d92807b2484c04801ec7405f8e42501c00f61001ec1803d82007b0200f600, 0xf60a, 0xf60a, 0xf602, 0x1ed3a03da6807b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x2701c00f602, 0x229e00753a14027001d42803a82006cc20629240c31e803a1000741800e82001d02003a00, 0x229e00753a14827001d42803a82006cc203d93407b1c803a1000741800e82001d02003a00, 0x229e00753a10027001d42803a8201ecca06292407b1c803a1000741800e82001d02003a00, 0x2289004504008a04200400022620044c214818001125003e490a00900088f40111d00221000441800882001102002200, 0x220a, 0x61a740c34281868205c4c40b89280c31d018610030c180618200c302018600, 0x32d1a065a280f91d019610032c180658200cb02019600, 0xfa6817349003e8d007d1401ba1800b1d003e10007c1800f82001f02003e00, 0x220a, 0x3da7407b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x3352a066a4812325019a100334180668200cd02019a00, 0x8a680114a80229205cd14011a1800f2500221000441800882001102002200, 0x2202, 0x3da7407b4280f68201ecc403d92807b1d00f61001ec1803d82007b0200f600, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x2202, 0x2202, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x229d004534008a4801f450022860004c40089842a03000221000441800882001102002200, 0x2202, 0x229e00750403da042404000221000441800882001102002200, 0x229e00750403da042504000221000441800882001102002200, 0x2206, 0x2206, 0x2202, 0x229d004534008a4801f450022860004c40089842b03000221000441800882001102002200, 0x2202, 0x229e00750403da042604000221000441800882001102002200, 0x220a, 0x220a, 0x2202, 0x2202, 0x8a740114d002292007d14008a180013100221000441800882001102002200, 0x220a, 0x220a, 0x2206, 0x229d00450a008a080113902ee6a0044c4008928011248560480044740ba8e42a01c00221000441800882001102002200, 0x0, 0x0, 0x0, 0x0, 0x220a, 0x220a, 0x0, 0x220a, 0x0, 0x220a, 0x0, 0x220a, 0x460a, 0xe20a, 0xe60a, 0x1f3500221000441800882001102002200, 0x1f4500221000441800882001102002200, 0x9b9281331d005e1000bc1801782002f02005e00, 0x9c9281351d00421000841801082002102004200, 0x2c03600460e, 0x8cee0119cc0213780426b008cce02e98c04b2b809653015c9e02992c02f1f80263b015c1e1800380230680400c008c1617802802304804008008c0e17001802102804004008c0616800800700804000, 0x2342804682008d0219020002332804662008cc21881800232680464a0084920101200231e80463a001c720100e00230800460c008c1001181002301004600, 0x468501750202b99405330805e5500bc9a0099240071e800e3a001c720100e000708000e0c001c1000381002301000e00, 0x11a0817940866080008cca0119880232680464a008c740038e43101c004610008c1801182002302004600, 0x11a140234100466205e4c21981800232680464a008c740038e43201c004610008c1801182002302004600, 0x1701203401c004606, 0x2f024004606, 0x30028004602, 0x35d1a06aa240d73681aa6901f4aa03e9480212880405003547c0098e807d0800fa0c01f41001181807d0200fa00, 0x8d1a011a2402336804669008caa01194802128804050008c7c06c8e80230800460c008c1001181802302004600, 0xac00045380089d001136004654, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2d01c00460a, 0x460a, 0x2f038004602, 0x30038004602, 0x1f4a401194431028004610008c1801182002302004600, 0x1f4a401194432028004610008c1801182002302004600, 0xe20a, 0xe202, 0xe202, 0x1f4a401194433028004610008c1801182002302004600, 0x221000441800882001102002200, 0x221000441800882001102002200, 0xe60a, 0xe602, 0xe602, 0x221000441800882001102002200, 0x221000441800882001102002200, 0x2202, 0x2202, 0x334e816262023c740488e40c01c00661000cc1801982003302006600, 0x1fd3a06998808f1d00fe1001fc1803f82007f0200fe00, 0xbea040b53682f6650394920718f40e31d01c610038c180718200e30201c600, 0x3503a00220a, 0x220a, 0x36024002202, 0x2202, 0x3c4da0789a817f1d01e21003c4180788200f10201e200, 0x1c4ea0389c81812500e21001c4180388200710200e200, 0x3e9d007d34002a4801f46803e8a00150c0049880091d003e10007c1800f82001f02003e00, 0xfa0801f3100221000441800882001102002200, 0xfa2801f3500221000441800882001102002200, 0x154f018e82023c740378e40d01c002a1000541800a82001502002a00, 0x1d53c063a0808f1d00ea1001d41803a8200750200ea00, 0x65a341834280366103ec9207c8f40f91d01f21003e41807c8200f90201f200, 0x3704a00220a, 0x220a, 0x2202, 0x38024002202, 0x40d1a081a281851d020610040c1808182010302020600, 0x4252a084a481872502121004241808482010902021200, 0x0, 0x0, 0x0, 0x220a, 0x0, 0x220a, 0x0, 0x220a, 0x113900221000441800882001102002200, 0x114900221000441800882001102002200, 0x474e816e6202949404e92417024008e10011c1802382004702008e00, 0x1cd3a0299880a52500e61001cc180398200730200e600, 0x88a041133a82266504449a0889281131c82221004441808882011102022200, 0x3903a00220a, 0x3a030002202, 0x2202, 0x229d004534008a5401149000a8a00150c00698800d2500221000441800882001102002200, 0x8a280113500221000441800882001102002200, 0x8a280113500221000441800882001102002200, 0x194f00ba8202949403b9241802400321000641800c82001902003200, 0x1c53c02ea080a52500e21001c4180388200710200e200, 0xca5401942803661048c9a0919281251c824610048c1809182012302024600, 0x3b04a00220a, 0x2202, 0x3c030002202, 0x0, 0x0, 0x3e02, 0x0, 0x2202, 0x0, 0x1891d003e10007c1800f82001f02003e00, 0x18b2500221000441800882001102002200, 0x114f00229d0f413800ea0801b3100221000441800882001102002200, 0x114f00229d0f813800ea0801b3100221000441800882001102002200, 0xa280114487e088004504008a04200400022620044c21f018001125003e490f40900088f40111d00221000441800882001102002200, 0x29e00453a10027000d4900128a00050c008a143f0420002650004c40b292414f1c80021000041800082000102000200, 0x40042002202, 0x41040002202, 0x0, 0x0, 0x3e02, 0x0, 0x2202, 0x0, 0x18d1d003e10007c1800f82001f02003e00, 0x18f2500221000441800882001102002200],
  [0x453e008a6c0114b80229300451e00fa2c01143803a830044ee0089cc01137803e6b0044ce00d98c0232b80425300649e00b92c0151f80263b0044260280480110880001000441e0200380110680000c0044160180280110480000800440e01001801f0280000400440600800800100800000, 0x455a00eaa4011428036810064ca00b9840152680264900046c0008d40001a0002320004620000c00010a00021000041800082001101000200, 0x480480100801000e00401800882c0000500200801c00c00801006001002000, 0x22c5004582008a740114c8022760044e400f9b801f350022660044c40088500110800020e00441800882001102002200, 0x457a039ae40135880229501c522014a240233a802271004cd200998401f2b0026550000a80099480012700264d0000980099280251f00de3d0280780098500130800260c00441400982001302002600, 0x1156802aaa0055520682a001142802a8201d50206020001132802a6200bcc20581800252900de510280a000a93401525003e4900009000a8f40151d00023900007000a85001508002a0c00541000a81001101002a00, 0x458a036b040175c80229d01ad32020a440113b002e750000e800b9c80373700226a0004cc00b99400032002e62005ca401e9380772681c04c004c7200b8500170800220e005c1800b82001702002e00, 0x11568032aa0065520882a00114280328201c50208020003d3500ee690380d000c994019310022610000c00089340192500424903c09000c8f40191d00023900007000c8500190800320c00641000c81001101003200, 0x36ce00459a09833001b648036c100453c00da740004e00369a01c52c035a480754700e28a00050c00da1400042003682006ce40279a801b3300f2650480c800d85001109003610006c1800d82001b02003600, 0x8b34011568022aa0045520b02a001b4500f289048110008a1401141002281000100008994011310022610540c000893401125003e490500900088f40111d0002390000700088500110800220c00441000881001101002200, 0x22ce00759a00033001d650022c600758a0c031001b610032be01b57400aad8073590002ae00755a0002b001d55003a9a00752402ca2801d4300f68505c10800885801d0a003a1000741800e82001d02003a00, 0x8b3801d5900f6b105c160008ab4011550022a9000150008a140114100228106c100008994011310022610680c000893401125003e490640900088f40111d0002390000700088500110800220c00441000881001101002200, 0x456a00fac401146803e89008cda0109a401f23003e4500008800f90801f2080004000547c0098e801f0a003e10007c1800881801f02003e00, 0xf00480200803a00e00801800882c0000500400807000c01001006001004000, 0x22c5004582008a740114c8022760044e40089b80113500026600dcc400885001108003e0e00441800882001102002200, 0x11628042c100453a025a640113b0042750000e80109c801f3700426d0000d80109a802f3300226201f4ac0119541f02a002e4a004c740108500210800220e00841801082002102004200, 0x11568046aa01cd521102a00114280468201c50210820007d3900467107c0e0011994023310022610000c001193402325003e490000900088f40231d000e390800700118500230800460c008c1001181001101004600, 0x459a00fb2401f6280229e007d3a00027001f4d00e296012d2400fa3801f4680008c007d14019a1807141009672007cdc0089b423036009e6200a47400f85001109003e10007c1800f82001f02003e00, 0x456a008ac401f4900229108c120008a34011450022890001100089b4011348022550044a400f9440002800223e0004740088500110800220c00441000881801102002200, 0x459c00fb3400066003eca00458c00fb080735f0042ba007d6c00fad40005a003eb200555c039aa801f4f004292007d1c008a342404600b282004c7400885801f0a003e10007c1800f82001f02003e00, 0x7d74008ae42405c0022b5004564008ac40005800228d0045120089b4011348022550044a400f9440002800223e0004740088500110800220c00441000881801102002200, 0x457a008ae40114a8022910044bc0089740002e00225a0044b20001600232b00425200649c00b9280110a00221000441400882001102002200, 0x1300480300804a00e00c01800882c0000500600807000c01801007001006000, 0x22bd004572008a54011488022750044e200f9580232900024e008c940088500110800220c00441400882001102002200, 0x459a008b240116280229e00453a0002700114d00229600452a0002500114900ea8e012d14023a1806b410022760044ea1381d004b350036620104940088500110900221000441800882001102002200, 0x457a008ae40114d00229909c130008a54011490022910001200089d4011390022710000e000895801f2900224e0004940088500110800220c00441400882001102002200, 0x459c008b34000660022ca00458c008b080115f0022bd000178008ae807f5b0042b200655c036aa80114f00229600452a14025002145003a82005c940088580110a00221000441800882001102002200, 0x4584008b04280600022bd004574008ae40005c0022950045220089d4011390022710000e000895801f2900224e0004940088500110800220c00441400882001102002200, 0x458a008b040113f00227d0000f80089e80113c8000780044ec0089c801137003e6a0044cc00d9880110a00220e00441800882001102002200, 0x1480480400804a00e0100180e80280400401000601000800880c00001008000, 0x22ad004552008a14011408022650044c200f9340112480023d0044720088500110800220c00441000881001101002200, 0x11670022cd000198008b28011630022c5000188008b080115f0022ba00456c00fac8011570036aa00453c008a742a04e003a82006cc40088580110a00221000441800882001102002200, 0x11650022c90a8190008b14011610022c1000180008ae801f590022ae00453a008a680114c80009800452400fa28011430022760044e40089b801f350022660004c40088500110800220e00441800882001102002200, 0x454c008a94000520022a20045420002800114f00229a00452c008a4801147003e8a00450c00ea080110900221000441800882001102002200, 0x1480480500804c00e0140180f00280500401200601400800880c0000100a000, 0x22ad004552008a14011408022650044c200f9340112480023d0044720088500110800220c00441000881001101002200, 0x100d00201800020e, 0x180d00301800020e, 0x2011004020000202, 0x2811005020000202, 0x80d001018003e0e, 0x2d00900c0100b001c0300300200500c00800400c0300102b00100c000, 0x220e, 0x40d80081902e01e00420a, 0x1802a02f0400020600b80a00081200101c00460e, 0x40e800819031026003e0a, 0xc40d00081800101c003e0e, 0x413800821032032003e0a, 0xc81100082000101c00220e, 0x41980082b033042003e0a, 0xcc1600082a00101c00220e, 0x81100102000220e, 0x3500900e0100d001c0380300300500e00800400c0380102b00100e000, 0x220e, 0x40e80081b03602a00220a, 0xd80e00081a00102800220e, 0x41380082303703600220a, 0xdc1200082200102800220e, 0x41980082d03804600220a, 0xe01700082c00102800220e, 0x81700102c00220a, 0x41380082503903a00220a, 0xe41300082400103800220e, 0x41980082f03a04a00220a, 0xe81800082e00103800220e, 0x81f00103c00220a, 0x3b00901001001001c040030340050100080b000c04001001001010000, 0x220e, 0x41980083103c04e00220a, 0xf01900083000104c00220a, 0x82900105000220a, 0x3b00901201001401c048030350050120080b400c04801001001012000, 0x220e, 0x101e00260e, 0x7e0a80f81001e81200101c002a0e, 0x102a002e0e, 0x840a81041000081204001c00320e, 0x8b38011668000cc004594008b18011628000c4004584008af80115e8000bc00457400fad80115a8000b4004564000ab8011568000ac0045540088580110a00221000441800882001102002200, 0x10660020c40041780082d00105600220a, 0x8ab4011550022a9000150008a1401141002281000100008994011310022610000c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x10540020800040c00081200101c00220e, 0x2183300104e00360a, 0x8c0a80041002281204401c00220e, 0x833047062003a0a, 0x20a81281002481204801c00220e, 0x220a, 0x458a00fb040114e803e990044ec0109c801f37003e6d0000d800f9a801533002262004c7400f85001f0800020e007c1800f82001f02003e00, 0xfae40115a80e6b1007d22008a3407144804271008cda0089a401f2a803e52007ca20001400152700223e004c7400f85001f08003e0c007c1001b81801f02003e00, 0x220a, 0x458a008b040114e8022990044ec0089d40003a002272007cdc0109a801933002262005c940088500110800020e00441800882001102002200, 0x8b040115e8022b9004532008a54011488022750044e40089c40003800426a0064cc01195801f2900224e005c940088500110800220c008c1400882001102002200, 0x22cd004592008b140114f00229d000138008a680114b002292007d1c00fa2801143002282006cc40088500010900221000441800882001102002200, 0x8b24011628022c100453a008a680114c80009800452400fa28011430022760044e40089b801f35002266006cc40088500110800220e00441800882001102002200, 0x22ce00459a000330011650022c6004584008af80115d003eb6007d64008ab80115500229e0075040008580110a00221000441800882001102002200, 0x8b28011628022c20045820003000115d003eb200455c008a740114c8022760044e40089b801f350022660074c40088500110800220e00441800882001102002200, 0x2202, 0x2202, 0x41a7c0834d810697020d26041a3c083458106870225062802080833b810673020cde0419ac08333810e6313c0c404195c0832981064f0214962681284e02489804802047e0500f40831d81403a020c262a004808308814010022c1e2980380830681400c020c1629002808304814008020c0e28801808302814004020c0625800808100814000, 0x20d6a046ac4025550026a915c150046a3408344804a8200a5022b020008336804a690094c401298455030004a550094a40419440a028004a4d0094940408f80251e81403c00947401285002508004a0c00941004181802502004a00, 0x20d6a037ac40895501068d01bd12043a080833680de690204c40379845803000de5501bca40419440a02800de4d01bc940408f806f1e81403c01bc7403785006f0800de0c01bc1001b81806f0200de00, 0x135c8026a900a522014a040133a802672004cdc00b9b42003600de660094ca2d01900132b00ee5516c0a8009928013248b2048004c7a0098e80130a002610004c1800982001302002600, 0x201e00260e, 0x4d82014a640133a802672004cdc0109b40f036004a6601bcca2e01900132b0046551740a8001928013248b2048004c7a0098e80130a002610004c1800982001302002600, 0x12c900258a014a740294d00529200a51c00fa3414046011e8602450a2f02100293900526e0044da2f81b00093100524900a47a0148e80290a00521000a41801482002902005200, 0x26cd004d94004b080135d0026b6007d6a0c82d008f5700dead180158005a780134900268e00451a30823000b41002649004c7a0098e80130a002610004c1800982001302002600, 0x115e8022b900452a008a440113a8022710044ac00f94801127006e4a1440780088500110800220c004c1400882001102002200, 0x8b38011668c60cc004594008b18011628c40c4004584008af80115e8000bc00457400fad80115a8000b4004564000ab8011568000ac0045540088580110a00221000441800882001102002200, 0x11b14011568046aa01cd523282a00234e802285008d04038a0464040004272008ce22e81c003d3500ee6916c0d0011994023310022610000c00119340232500424903c09000c8f40231d000e390800700118500230800460c008c1001181001101004600, 0x459c038b346706600e2ca00458c038b140006200e2c201c57c038af46605e0022ba007d6c038ad40005a00e2b200055c038ab40005600e2aa01c4e40088580710a00e21001c4180388200710200e200, 0x8b340115e8022b900453c008a540114900229100012000fa28011448be088006d040089d401138802256007ca40089441402800224e0004940088500110800220c00441400882001102002200, 0x459c039b340006600e6ca00458c039b146906200e2c201cd7c039af46805e0022ba007d6c039ad40005a00e6b200055c039ab40005600e6aa01cd240088580730a00e61001cc180398200730200e600, 0x8b38011630022bd004574008ae40005c003eb20045623082c001d550022950045220089d401138802256007ca40089441902800224e0004940088500110800220c00441400882001102002200, 0xc0d80181905201e00260a, 0x100e80201b05302a002602, 0x2d800026f80045d8005b80013640022bc002560008a50023480026881a81000089500112601063c, 0x140e80281b05402a002602, 0x459c008b346c0660022c900453c008a746b04e00229a00452c008a540004a002292007d1c008a280014300228212c0700088500150900221000441800882001102002200, 0xaa7c0154d802a9700bd2600aa3c01545802a8700d50600a9dc03939802a6f0054d601999c03131806e5700bca601793c01725802a3f0094762a80e85801c8980380054263800480150881601000ec1e3780380150681600c00541637002802f0481600800dc0e368018015028160040054061e800800500816000, 0x1556802aaa0055523902a001542802a8200550238820001532802a6200bcc2058180025290102511340a000a93401525002a4902c09000a8f40151d000a3902c07000a85001508002a0c00541000a81001501002a00, 0x22c500858200aaf402f5c80229d012d3200aa540394880227600bcea0001d002f39005e7102c0e001b9b802135005e66005cc401b95802f29005e4e005c940128e806f1c89c03800bc2801784001107005e0c00541401782002f02005e00, 0xea9f01d53603aa5c02f4980ea8f01d51603aa1c0354180ea77012ce603a9bc07535806667013cc601b95c02f29805e4f005c9600a8fc0251d8ac03a01d4263b004807508818010024c1e3a80380750681800c01d4163a002802f0481800801d40e3980180750281800401d4061f000800500818000, 0x7556802aaa0055523b82a001542802a8201d50206020007532802a6200bcc238818002529010e5113c0a000a9340152500ea4903009000a8f40151d000a3903007000a85001508002a0c00541000a81007501002a00, 0x8b340756480eac501d582008a780754e80009c01d53403aa640c04c002296012d2403aa3801f45006686006d0403a9d804b3900ea6e01d4d403a99804f3100523a01d4280088480750800760e01d41803a8200750200ea00, 0x8ab4011550022a91e4150008a1401141002281000100008994011310022611e00c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0x2a9f00553600aa5c02149802a8f00551600aa1c05941802a7700e4e600a9bc0153580fe6700c4c601b95c0212980424f005c9600a8fc0131d8ae03a0054263e80480150881a01000ec1e3e00380150681a00c0054163d80280210481a00801fc0e3d00180150281a0040054061f80080050081a000, 0x1556802aaa0055520682a001542802a820055023b820001532802a6200bcc2390180025290112511400a000a93401525002a4903409000a8f40151d000a3903407000a85001508002a0c00541000a81001501002a00, 0x8b38015668000cc00559400ab240d0640022c601d584008af80215d002ab6007d6400aab801d55002a9e00553400aa5802149002a8e00551400aa180594100263a00442c00a85001509002a1000541800a82001502002a00, 0x8ab4011550022a9000150008a14011410022811fc100008994011310022611f80c000893401125003e490000900088f40111d0002390000700088500110800220c00441000881001101002200, 0xf40a81cc1003681200201c002a0e, 0x3d82a0740400060601480a00181200301c002a0e, 0x3e02a06f0400a60700100c00201208001c002a06, 0x3b02c0700440a80700140d00281408101c002a02, 0x3ba7c0774d80ee9701dd2603ba3c0954580ee8701dd064382080773b80ee7301dcde04c9ac0773380ee632180c404b95c0772980ee4f03809a03b92c0e02500ee3f0254764200e88501c90603801dc264580480770881c010026c1e4500380770681c00c01dc164480280770481c00801dc0e4400180950281c00401dc064100080770081c000, 0x1dd6a04eac403d55002ea923815004ea3407744807a8201050246820003d36807a6a01dcd20701a003d32807a62025caa00994403d25007a4923009003b8f803d1e81c03c00f47401e85003d08007a0c00f41003b81803d02007a00, 0x1dd7a03bae40775500ee9501dd2203ba080773a80ee7201dce20701c00773280ee6201dcac04f9480772700ee4d03809803b9280771d012a3923c07003b8500770800ee0c008c1403b8200770200ee00, 0x80d80101908801e002e0a, 0x5d82020a640173b005e7502c0e800b9b401735007a660284ca48019007d2b0146552440a800b9340172500063a004c722c80e00170a002e10005c1800b82001702002e00, 0x1baf401156806eaa01fd524982a00374a80228500dd0403aa049204000fa7200bce24881c002332806e6200bcc20581800252900de511680a001b93403725003e4900009000a8f40371d000e3908007001b85003708006e0c00dc1001b81001101006e00, 0x3032002e0a, 0x1ac900358a020a740414d00829600452a0a825004145014a8602750a4a02100413b0022752540e80209a800d3100824d0104940148e40410a00821001041802082004102008200, 0x2ecd005d94006b080175f0022bd06817800bac80a55700eead258158007a780174b00229525c12800ba2800f41002e4d005c940098e40170a002e10005c1800b82001702002e00, 0x115a8022b100451a008a24011368022692240c800895401f2880223e008c740088500110800220c00441000b81801102002200, 0x459c035b349906600d6ca00458c035b140006200d6c200457c035af40005e00d6ba01d56c035ad49805a0022b200055c035ab40005600d6aa01d4d400885806b0a00d61001ac1803582006b0200d600, 0x8b34011628022c100453a008a680114c800098004524008a449504800228e006d040089d8011390022710540e00089b801f350022660004c40088500110800220e00441800882001102002200, 0x459c036b340006600daca00458c036b149b06200d6c200457c036af40005e00daba01fd6c036ad49a05a0022b200055c036ab40005600daaa01fd1400885806d0a00da1001b41803682006d0200da00, 0x8b38011628022c20045820003000115d0022b925c170008ad801d5500229d0045320089d8011390022710680e00089b801f350022660004c40088500110800220e00441800882001102002200, 0x101380202308a036002e02, 0x4380002ef80045e8007ba0017640022c4003570008a700374c002e902701000089d00113200ee4c, 0x141380282308b036002e02, 0x459c008b349e0660022c900453c008a749d04e00229a00452c008a4801f4700228d000118008a28001430022822080900088500190900221000441800882001102002200, 0xca7c0194d80329700652600ca3c0214580328701250600c9dc0193980326f012cd602399c045318046570084a600c93c03d2591804a23c09241812002f1f80263b0064265100480190881e01001341e5080380190681e00c008c165000280190481e00800640e4f80180210281e0040064062000080050081e000, 0x19568032aa0065525202a00194280328200650251820003d3500ee692100d000c9940193100326103c0c000c9340192500424903c09000c8f40191d000a3903c07000c8500190800320c00641000c81001901003200, 0x22bd00857200cad402158802295012d2200ca3404b448046750084e20119b402134807a620254c242818001f2b0042550000a80109480212881e05000bc9c00992802f1f00263a0084280108400210600220a00841000c81802102004200, 0xe29f01c536038a5c0714980e28f008516038a1c0494180e27701c4e60389bc04b35808e67006cc601195c0212980324f00f49646812802f1f80263b01c42654004807108820010029c1e5380380710682000c01c4165300280710482000801c40e5280180210282000401c40620800800500820000, 0x71568032aa0065525482a00194280328201c50208020003d3500ee692180d000c9940193100e2610400c00389340192500424928c09000c8f40191d000a3904007000c8500190800320c00641000c81007101003200, 0x8b340716480e2c501c582008a780714e80009c01c534038a641004c00e296004524008a3804b45008e86006d040389d80713900e26e012cd403899801b3100824a01c42800884807108009a0e01c4180388200710200e200, 0x8ab4011550022a92ac150008a1401141002281000100008994011310022610000c000893401125003e492a80900088f40111d0002390000700088500110800220c00441000881001101002200, 0x329f00653600ca5c0194980328f00851600ca1c01d418032770064e600c9bc04b3580e6670114c601195c0212980324f005c9647012802f1f80263b0064265780480190882201001341e5700380190682200c01cc165680280190482200800640e5600180210282200400640621000800500822000, 0x19568032aa0065520882a00194280328200650254820003d3500ee6921c0d000c994019310032610440c000c9340192500424929009000c8f40191d000a3904407000c8500190800320c00641000c81001901003200, 0x8b38019668000cc00659400cb24110640022c601c58400caf80115d0022b600856400cab801d5500329e00653400ca580194900328e00851400ca1801d41002e4a00442c00c8500190900321000641800c82001902003200, 0x8ab4011550022a9000150008a14011410022812c4100008994011310022610000c000893401125003e492c00900088f40111d0002390000700088500110800220c00441000881001101002200, 0x5602a0a50400040602200a00101200201c00320e, 0x15a0a82981005001200301c00320e, 0x5702a08a0480080802840c0020120b201c003206, 0x5402c08b04800a0882880d0028140b301c003202, 0x794f97609e01e53603ca5c0794980f28f02a51603ca1c0794196e08201e4ee03c9cc0a93780f26b01e4ce0901940793182406201e4ae05594c0792780f24b2d809403c8fc0a91d96a03a01e4265e00480790882401001e41e5d00380790682400c01e4165c80280790482400801e40e5c00180a90282400401e4065a000807900824000, 0xdb38011669800cc01e56a00dac401b550036a92fc15000da3401b4500f28904811000da1401b4100f26d02bcd200d98801b3097c06002b4aa03c94401b25009e492f409003c8f801b1e82403c006c7400d85001b0800360c006c1003c81801b02003600, 0x3cb380796280f2c101e55403ca740794d00f29904813003ca140794100f27601e4e403c9b80a93500f26601e4ca0901900793100f24a01e47403c8500790800220e01e41803c8200790200f200, 0x1820cc008138010210b803200360a, 0x4f64809ec6007d8a62031004f4f00ea9d030138028a4804f46809e8a02c50c056a14c204200ea7202ccdc05a9b4c3036009e65013cc40048e804f0a009e10013c1802782004f02009e00, 0x115a80eab102cd2405aa44c304800228d01d51403aa240c04400a6750044da0309a40752a80ea52007ca200014002925002a3e00047403a8500750800ea0c01d4100088180750200ea00, 0x18a0cc00c138018210b903200360a, 0x1b648036c600458a64031001b4f00e29d04013800da5401b4900a28a02dd0c03ca14c604201727602ecea6381d007135003665006cc400692801b0a003610006c1800d82001b02003600, 0x115e80e2b902e53405ea64c704c00229501c524038a441004800e27501c4e40089c40003800466e0104c40089580212900324e0004940388500710800e20c0044140388200710200e200, 0x64833004046003602, 0x1b668036ca006d8c008b141b0620036ba013d6400dab8079569940ac006d3c008a74cb04e000282006cca00d98801b0a003610006c1800d82001b02003600, 0x455a008aa8011549980a82e8118008a14011408022650044c205393401f2480223d0044720088500110800220c00441000881001b01002200, 0x8b3801b668000cc006d94008b1801b628000c4006d84038af806b5d00eab601c564000ab801b568000ac006d5400885801b0a003610006c1800d82001b02003600, 0x453e008a6ccd04c802297004526008a3c01f458022870005060089dc011399900720044de00f9acc40350022673000cc00d98c0232b80a25300649e01f92c0151f804e3b0044266700480110882601000441e6480380110682600c0044166280280110482600800440e60801801f0282600400440621800800100826000, 0x22ce006d9a09833001b650022c6006d8a09831001b6100e2be01ad7403aad8071590002ae006d5a0982b001b55003699006ce40279a801b3300f2652ec0c800885801b0a003610006c1800d82001b02003600, 0x22ce00459a098330011650022c9000190008b18011610022c132c180008af80115d0022b6007d64008ab801d5500229e004534008a641b04c002296004524008a3801f450022860005040089c801f3500226600442c0088500110900221000441800882001102002200, 0xa0cc0141686782b0bc046003602, 0x458c008b14d20620022c100453a008a64b40400022760044ea6881d001139003e6e0044da6801b0011350002660044c40088500110800220e00441800882001102002200, 0x114f9ac09d004536008a5c0114980228f007d16008a1c01d418022770044e60089bc01f35802267006cc65e81880572b809653011c9e02092c0331f80523b0044266b80480110882801000441e6a80380110682800c0044166a00280110482800800440e69801801f0282800400440622000800100828000, 0x8b34011568022aa0045526c82a001b4500f2892d4110008a1401141002281050100008994011310022613600c000893401125003e490500900088f40111d0002390500700088500110800220c00441000881001101002200, 0x7d9a008af401f5c8022b5007d62008a5401f4880228d007d12027a080233a809671015cda0259a401f2b003e550000a800f94801f2882805000cc9c0099280151f00523a007c2800f84001f0600220a007c1000881801f02003e00, 0x114f9ba09d004536008a5c0114980228f007d16008a1c01d418022770044e60089bc01f35802267006cc65f01880572b809653011c9e02092c0331f80523b0044266f00480110882a01000441e6e00380110682a00c0044166d80280110482a00800440e6d001801f0282a0040044062280080010082a000, 0x8b34011568022aa0045526f82a001b4500f2892d8110008a1401141002281054100008994011310022610540c000893401125003e493600900088f40111d0002390540700088500110800220c00441000881001101002200, 0x459a008b14011608022bd004572008a740114c80229500452200da080113b0022750000e80089c80113882a070008cdc0259a804733002e62015cac0259480192700824a0044280088400110700220c00441400882001102002200, 0x114f9c609d004536008a5c0114980228f007d16008a1c01d418022770044e60089bc01f35802267006cc65f81880232b809653011c9e02092c0331f80523b0044267200480110882c01000441e7100380110682c00c0044167080280110482c00800440e70001801f0282c0040044062300080010082c000, 0x8b34011568022aa0045520b02a001b4500f2892dc110008a14011410022810581000089940113100226137c0c000893401125003e493640900088f40111d0002390580700088500110800220c00441000881001101002200, 0x8b38011668000cc004594008b24160640022c600458a0c0310011610022be004574008ad801f590022ae007554008a780114e9ca09c004534008a580114900228e007d14008a1801d4100366200442c0088500110900221000441800882001102002200, 0x8ab4011550022a9000150008a14011410022810001000089940113100226139c0c000893401125003e493980900088f40111d0002390000700088500110800220c00441000881001101002200, 0x7002a0b80440040803a00c06d01200201c00220e, 0x7082a0b90440060803a40c06a01200301c00220e, 0x1c40b03701106a81a004028002202, 0x459a008b2801161003eba00456c008aa8011549ca0a8000514008a24ea0440022820045020c0200011310022613740c000892801f249ac04800447a0088e80110a00221000441800882001102002200, 0x5e02e0050581bc08835c0d0028140eb01c002202, 0x7b4f9e609d01ed3603da5c07b49817e8f01ed1603da1c1704280f68305c10403d9dc07b3980f66f02fcd603d99c07b319de06201ecae06094c07b2780f64b3b809403d8fc0bf1d9da03a01ec267a004807b0882e01001ec1e79003807b0682e00c01ec1678802807b0482e00801ec0e7800180bf0282e00401ec0676000807b0082e000, 0x8b3801d669f00cc00756a00eac807b5882e0b000755a00eaa807b4680368900750400ea04f704000f66d0314d200e98801d309ec060030caa03d94401d2500b2493d409003d8f801d1e82e03c00747400e85001d08003a0c00741003d81801d02003a00, 0x3db3407b6500f6c905c19003db1407b5680f6aa01ed3c03da6807b4b00f69201ed1c05fa2807b4300f68505c10803da0807b3100f64a01ec7403d8500110900f61001ec1803d82007b0200f600, 0x40cc3e41880102b0f0042003a0a, 0x5967002acd03419802cb0805b5d00b2b5016564063ab80c3569f40ac007d3c02ca74fc04e00fe9203251c065a34fb04600b2850165040058e80590a00b21001641802c8200590200b200, 0xc95d0196b93ec170008ad401559002ab1034160008a340754480ba750044da0109a40152a802a52007ca200014001325002a3e00047400a85001508002a0c00541000881801502002a00, 0x60cc3f41880182b0f1042003a0a, 0x1d670032cd04419800eb0801d5e803aba016d6402eab807b569fc0ac00453c00ea750004e019a96033d2a7f825007345003a8500750400792801d0a003a1000741800e82001d02003a00, 0xcd610032c13fc180008af40195d0032b9044170008a54071488032750064e40089c40003800466e005cc40089580212900324e00049400c8500190800320c00441400c82001902003200, 0x80cc0101688082b0f2046003a02, 0x1d670022cd05819800eb1401d61003aba01656400eab807b56a040ac00453c00ea750304e003a8500750400098801d0a003a1000741800e82001d02003a00, 0x453e008a6ce304d00229700452680024801147803e8b3f0114008a1cf8043003a830044ee0089cc01137803e6b0044ce00098c0232b80b653011c9e00392c0331f80563b0044268280480110883001000441e8200380110683000c0044167e80280110483000800440e7c801801f0283000400440623800800100830000, 0x22cd004594008b25030640022c5004584008b04160600022ba007d64008ab80114f00229d060138008a680114c80009800452c008a4801147003e8a00450c00da080113b0022720044dc00f9a8011330002620044280088480110800220e00441800882001102002200, 0x22ce00759a0c033001d650022c600758a0c031001d6100e6be01b57403fad8073590002ae00755a0c02b001d55003a9a00752402ca2801d4300f6853cc10800885801d0a003a1000741800e82001d02003a00, 0x8283300505a003a02, 0x3d0168008ab401154802285004504008a05060400022650044c206893401f2480223d0044720088500110800220c00441000881001d01002200, 0x458a008b04ec05400229e00453a8482700114c8022760044ea8401d001139003e6e0044da8381b0011350002660044c40088500110800220e00441800882001102002200, 0x114fa1a09e004536008a5c0114980228f007d16008a1c01d419ea0820044ee0089cc01137803e6b0044ce00d98c0232b80425300649e00b92c0151f80263b0044268700480110883201000441e8600380110683200c0044168580280110483200800440e85001801f0283200400440624000800100832000, 0x8b3801d5900f6b13b4160008ab4011550022a9064150008a14011410022814401000089940113100226143c0c000893401125003e490640900088f40111d0002390640700088500110800220c00441000881001101002200, 0x7d9c008af401f5c8022b5007d6202caa80114a803e9100451a00fa240233a804271008cda0109a401f2b003e550000a800f94801f2883205000549c0099280151f00263a007c2800f84001f0600220a007c1000881801f02003e00, 0x114fa2809e004536008a5c0114980228f007d16008a1c01d419ec0820044ee0089cc01137803e6b0044ce00d98c0232b80425300649e00b92c0151f80263b0044268a80480110883401000441e8980380110683400c0044168900280110483400800440e88801801f0283400400440624800800100834000, 0x8b3801d5900f6b13b8160008ab4011550022a9068150008a1401141002281458100008994011310022610680c000893401125003e4943c0900088f40111d0002390680700088500110800220c00441000881001101002200, 0x459c008b14011608022bd00457200eaa80114e80229900452a008a440113b0022750000e80089c801138834070008cdc0109a801933002e62008cac01094801927002e4a0044280088400110700220c00441400882001102002200, 0x114f99a09e004536008a5c0114980228f007d16008a1c01d419ee0820044ee0089cc01137803e6b0044ce00d98c0232b80425300649e00b92c0151f80263b0044268d00480110883601000441e8c80380110683600c0044168c00280110483600800440e8b801801f0283600400440625000800100836000, 0x8b3801d5900f6b13bc160008ab4011550022a906c150008a140114100228106c100008994011310022614580c000893401125003e494400900088f40111d00023906c0700088500110800220c00441000881001101002200, 0x8b38011668260cc004592008b1801162a360c400458200eaa80114f00229d000138008a680114c83609800452c008a4801147003e8a00450c00da080113b0022720044dc00f9a8011330036620044280088480110800220e00441800882001102002200, 0x7802c00205422e0804700c08881200201c00220e, 0x7882c0030542300804740c08581200301c00220e, 0x7902e0040582260884300d00201411e01c002202, 0x459a008b2801161003eba00456c008aa801154a360a8000514008a251f044002282004502098200011310022614500c000892801f24a1a04800447a0088e80110a00221000441800882001102002200, 0x2340b04541108701a005028002202, 0x1811003020003e0e, 0x201700402c003e02, 0x281700502c003e02, 0x80e801019120026006e0a, 0x4800d00101800201c00020e, 0x101100202000220e, 0x12200903801048401c0e00300300503800800800c0e00102b001038000, 0x220e, 0x80e80101b12302a00220a, 0x48c0e00101a00202800220e, 0x81380102312403600220a, 0x4901200102200202800220e, 0x81980102d12504600220a, 0x4941700102c00202800220e, 0x101700202c00220a, 0x24e0cc0081380102512603a00220a, 0x4981300102400203800220e, 0x40cc4a41880102f12804a00220a, 0x4a01800102e00203800220e, 0x101f00203c00220a, 0x12a00903a01001001c0e80312100503a0080b000c0e80100200103a000, 0x220e, 0x81980103112b04e00220a, 0x4ac1900103000204c00220a, 0x102900205000220a, 0x12a00903c01001401c0f00312200503c0080b400c0f00100200103c000, 0x220e, 0x458a036b040114e80d6990044ec01b9c80153700226a0004cc01b99400032006e6200dc7201b85003708003e0e00dc1801b82003702006e00, 0x22ad01cd52008a1407140802e690064ca0089840152a80224d004c920008f40011d0002390000700008500010800020c00041000081001f01000200, 0x203600420a, 0x25c0a84b41000101212c01c00460e, 0x20660040c40081780102d00205600220a, 0x20540040800080c00101200201c00220e, 0x204e003e0a, 0x204400220e, 0x2066003e0a, 0x205800220e, 0x220a, 0x458a008b040114e8022990044ec0089d40003a002272008cdc0089a800133006e6200dca400885001108003e0e00441800882001102002200, 0x22bd004572008a54011488022750044e40089c40003800466e005cc40089580212900324e005c940088500110800220c008c1400882001102002200, 0x11670022cd4bc198008b240114f00229d000138008a680114b00229200451c008a280014300d682007cd400885001f0900221000441800882001102002200, 0x8b34011628022c100453a008a680114c800098004524008a3801b410022760044e40089b801f35002266034cc40088500110800220e00441800882001102002200, 0x11670022cd000198008b28011630022c54c0188008b080115f0022ba00456c008ac80015700daaa007d1400f8580110a00221000441800882001102002200, 0x8b38011628022c20045820003000115d0022b6007554008a740114c8022760044e40089b801f35002266031cc40088500110800220e00441800882001102002200, 0x2202, 0x2202, 0x22ad00bd54010aa53205400228500bd04025a0531040007a6a0284d24801a001932805e6200bcc20581800252900de511700a000a93402f2500424903c0900178f402f1d00023900007001785002f08005e0c00bc1001781001101005e00, 0x11a7c0234d804297008526011a3c05d45804687008d069c020804b3b809673015cde0299ac023338046634dc0c401795c0132980464f07c09a01092c1f02500463f001c769a80e93601ca68038015c269d80480230883e010008c1e9d00380230683e00c008c169c80280210483e008008c0e1700180070283e004008c069980080230083e000, 0x35d7a06aae407d5501ae9503552203ea0807d3a80fa720084e20f81c007d3280fa620354ac0099480232700fa4d07c09803e92807d1d0006394f007003e85007d0800fa0c008c1403e82007d0200fa00, 0x8d7a011ae402355004695008d22011a080233a8046720084e20f81c002332804662008cac06c9480232700464d07c0980119280231d000e394f40700118500230800460c008c1401182002302004600, 0x303600420a, 0x11568022a900450a008a053903a0022650044c20089340232480223d0004720088500110800220c00441000881002101002200, 0x8b3400564800ac500453c025a740004e00969a00452c025a540004a009692007d1c025a340004600968a00150c008a080513100824a00a47402585001109009610012c1802582004b02009600, 0x8b24011628022c100453a008a680114c80009800452400fa28011430022760044e40089b801f35002266006cc40088500110800220e00441800882001102002200, 0x8b38021668000cc008594008b18005610022be00857a0002f00215d003eb600856a0002d002159000aae004554002a7805b41002e4a004c740088580210a00421000841801082002102004200, 0x8b28011628022c20045820003000115d003eb200455c008a740114c8022760044e40089b801f350022660074c40088500110800220e00441800882001102002200, 0x101380202513a03a004202, 0x21820042fc0045e8002bc13e0660022c40045380089d001136004654, 0x4f8200010be0005780042c8001580008a700214c00c2900085100089d001136004654, 0x141380282513b03a004202, 0x459c008b35400660022c900453c008a753f04e00229a00452c008a4801f4700228a00050c008a14000420022824cc0a00088500230900221000441800882001102002200, 0x11a7c0234d804697008d2601ba3c037458046870175060119dc02339806e6f00dcd602b99c053318046570084a69e01493d028a68050008c9e00b92c0371f80263b015c26a2004802308840010008c1ea180380230684000c008c16a1002802304840008008c0e96001803702840004008c06a0800800700840000, 0x23568046aa008d52a302a002342804682008d02a2820007d390046714d40e0011994023310046610800c001193402325006e490800900118f40231d000e390800700118500230800460c008c1001181002301004600, 0x22b5007562011ab405d5480228d006d1202ba1405340800672001ce29b01c002336802e69008cca00b9840372a80265100dc9a0099240011f000e3d0000780038e80071c840038001c2800384000706000e0800440c00381002301000e00, 0x1c53e038a6c0714b80e29301c51e03aa2c0714380ba8301c4ee0389cc0753780ea6b01c4ce00d98c0232b80425300649e00b92c0151f80263b01c426a480480710884201000641ea400380710684200c01c416a380280710484200801c40e9680180750284200401c4061780080db00842000, 0x71568046aa008d52a502a00234280468201c50210820007d390046714dc0e00119940233100e2610840c00119340232500ea490840900388f40231d000e395140700118500230800460c008c1001181007101004600, 0x116680e2c901c58a038b040114f00e29d000138038a680714c84209801c52c008a4807547003e8a00450c00da080713b00e27201c4dc03a9a80713300366201c42800884807108009a0e01c4180388200710200e200, 0x8ab4011550022a9530150008a1401141002281000100008994011310022610000c000893401125003e490000900088f40111d00023952c0700088500110800220c00441000881001101002200, 0x1cd3e039a6c0734b80e69301fd1e03fa2c07343803a8301ccee0399cc0733780fe6b01ccce02998c0232b804253011c9e00b92c0331f80263b011c26a780480730884401001cc1ea700380730684400c01cc16a680280730484400801cc0e97001807f0284400401cc061800080dd00844000, 0x23568046aa01cd521102a007342804682008d02a5020007d390046714e00e00119940233100e6610880c00119340232500fe490880900398f40231d000e395180700118500230800460c008c1001181007301004600, 0x116700e6cd000198039b28073648440c800458c038b080735f0022ba01fd6c00fac801157003aaa01cd3c039a680734b00e69201cd1c03fa2807343003a8200442c0398500df0900e61001cc180398200730200e600, 0x8ab4011550022a9000150008a1401141002281544100008994011310022610000c000893401125003e490000900088f40111d0002395400700088500110800220c00441000881001101002200, 0x29a0a851c1000181214201c00460e, 0xa702a13a04c0080800100c0a181215201c004606, 0xa482c13b04c00a0880140d0a201415301c004602, 0x33668022ad00cd5403faa55505401628a02b5126102200114280668201d502060200011328066620384c2aa018008f290122511780a000a93403325003e490500900198f40331d0002390000700198500330800660c00cc1001981001101006600, 0x8a7c0eb4d802297004526008a3c01145802287038d060739dc0eb3980226f08c0da0759ac2303501d267039cc600895c0112981ce4f0394960088fc0e31daac03a004426ad00480110884601000441eac80380eb0684600c004416ac00280110484600800440eab8018011028460040044061900080e300846000, 0x115e803eb9007d6a00fa5401f4901d69108c12000fa3401f4501e27503ace20779a40112b003e5508c0a800f9480b32700524a03b47400f85001f08003e0c00441400f82001f02003e00, 0x458a008b040114e80229a03ad321182600114680228a0044ec0089c80113700226d08c0d80089a80113301e662038c740088500110800220e00441800882001102002200, 0xc13801823158036003e0a, 0x3ecd00458a03aa780714e84209c012d2a025a480754701e28d56c11803aa080713b01ea755700e80259b404b3500e2620104940148e804b0a009610012c1802582004b02009600, 0x38b040115e80e2b901c534038a655c04c00229501c524038a442104800e27501c4e40089c40003800426a0064cc01195801f2900224e001c940388500710800e20c0044140388200710200e200, 0x404a003e02, 0x7d9400fb255d064003ec5007d84032ae801f59003eae007d3a00fa6800549003e8d007d14019a180ef39003e6e0024c40048e801f0a003e10007c1800f82001f02003e00, 0x11568022a9564128008a14011408022650044c20089340112480323d0004720088500110800220c00441000881001f01002200, 0x22ce007d9a00033001f650022c6007d8a00031001f6100e2be00157400fad801f5a8000b4007d64002ab807155003e9e007d3aae827005941009e6200247400885801f0a003e10007c1800f82001f02003e00, 0x459a008b28011648000c8004584008ae801f590022ae00453c008a680114b00229200451c00fa280114300ba820044e40088500110900221000441800882001102002200, 0x141980282f15a04a003e02, 0x115e81eeb9007552008a5401b4881da8a038d12ab02200794280327501ace200b9840752b00265200049c0009340002600024a021c7a0008500010800020c00441400082000102000200, 0x11628022c100453a008a65570440022760044e400f9b8011350002660044c40088500110800220e00441800882001102002200, 0x458a008b040115c80229d004532008a540ef450022760044ea0001d00113900ea6e0084d400c99806b31006e56005c940088500110800220e00441800882001102002200, 0x8b38011668000cc004594008b18011610022be004574008ad801f590022ae03dd54008a780114900228e0075040088580110a00221000441800882001102002200, 0x3eba00456a008ac8011588000b0007d24008a34011450022890001100089b40113500226957c0d000895401129003e510000a00088f80011d0022395780700088500110800220c00441000881801102002200, 0x5601200182200302800220e, 0x4038002202, 0x5681800282e005038002202, 0x1567018eb2030d627d02c001156802aaa0055520682a001142802a8201d502b0820001132802a620184c2b0018008f2900de511800a000a93401525003e4906409000a8f40151d00023900007000a85001508002a0c00541000a81001101002a00, 0x8a7c0ff4d81fa9703fd26008a3c2404681fe8b09011400aa1c0fd418022770044e60089bc01135802267006cc600895c0112980324f03ec960088fc0f91dac403a004426b300480ff0884801000441eb280380110684800c004416b200280110484800800440eb18018011028480040044061980080f900848000, 0x1f5e803eba03fd721202e001f5a803eb200452a00fa4401f4682067503fce20109a40112b003e550900a800f9480c92700264a04047400f85001f08003e0c00441400f82001f02003e00, 0x459a008b280ff648480c800456a008ac80114f00229a00452c008a480114700228d090118008a2801143020a8203e4740088500110900221000441800882001102002200, 0xc1980182d164046003e0a, 0xfece01cd9a11033001f630042bd008574083ad81035aace0b401fd54008a781094b0216955a0128010a340214500e682005c940098e80210a00421000841801082002102004200, 0x84b0807360ad00c000457a039ae80735c8440b801cd32008a540714880e67501cce40089c40003800426a011ccc01195801f2900224e001c940398500730800e60c0044140398200730200e600, 0x101980202f16504a003e02, 0x7d9400fb255d064003ec5007d84002ae801f5a803eb200555c00fa7401f4d00d292007d1400fa1806139003e6e002cc40058e801f0a003e10007c1800f82001f02003e00, 0x4592008b14011608022ba00453a008a680114c80009800452400fa28011430022760044e40089b801f35002266014cc40088500110800220e00441800882001102002200, 0x505e003e02, 0x16605e0022ad004552008a14011408022650044c200893401124808e3d0004720088500110800220c00441000881001f01002200, 0x115e803ab904056407cac56205800f6ad00452a00da4401b4080327501b4e200b9840152b00265200049c0009340002600024a04347a0008500010800020c00441400082000102000200, 0x11628022c158c160008a740114c8022760044e400f9b8011350002660044c40088500110800220e00441800882001102002200, 0x458a008b040115e8042b200453a008a64011488022760044ea0001d00113900fe6e0084d400c99806d31006e56005c940088500110800220e00441800882001102002200, 0x8b34011648022c500453c008a740004e00229a00452c008a4801147003e8a00450c00da080113900226e006cc40088500110900221000441800882001102002200, 0x5901700182c00302800220e, 0x5941800202e004038002202, 0x5038002202, 0x201f00403c002202, 0x281f00503c002202, 0xc0e80181916902600460a, 0x5a40d00181800301c00020e, 0xc0e80181b16a02a00460a, 0x5a80e00181a003028003e0e, 0x181700302c00220a, 0x2d80cc00c1380182516b03a00220a, 0x5ac1300182400303800220e, 0x60cc5b81880182f16d04a00220a, 0x5b41800182e00303800220e, 0x181f00303c00220a, 0x16f00904a01001001c1280312100504a0080d000c1280100300104a000, 0x220e, 0xc1980183117004e00220a, 0x5c01900183000304c00220a, 0x182900305000220a, 0x16f00904c01001401c1300312200504c0080d400c1300100300104c000, 0x220e, 0x457a039ae40114a80e2910064ea0089c402330803e56008ca40009380232680004c008c940118500230800460c00441401182002302004600, 0x22ad01b552008a1406b4080326d0044ca00b98401328802a4d007c920008f40011d0002390000700008500010800020c00041000081001101000200, 0x457a039ae40114a80e291008cea0089c402334803e56008caa0001500232900024e008c940118500230800460c00441401182002302004600, 0x22b5007d62008a3401f448046750044da0109a401f2a803e52007ca200014001325002a3e004c7400f85001f08003e0c007c1000881801f02003e00, 0x30660060c400c1780182d00305600220a, 0x305400608000c0c00181200301c00220e, 0x11670022cd5c4198008b240114f00229d000138008a680114b002292007d1c038a280014300e2820044e40088500110900221000441800882001102002200, 0x8b340115e8022b900453c008a540114900229100012000fa2801b410022750044e200895801f2900224e014c940088500110800220c00441400882001102002200, 0x11670022cd000198008b28011630022c55c8188008b080115f0022ba007d6c039ac80015700e6aa0045240088580110a00221000441800882001102002200, 0x8b38011630022bd004574008ae40005c003eb2007554008a54011488022750044e200895801f2900224e0174940088500110800220c00441400882001102002200, 0x304e00220a, 0x304c00220a, 0x306600220a, 0x306000220a, 0x2202, 0x2202, 0x47668022ad011d54039aa574054016e8a01e51263022001142808e8201c5020802000a535013a692500d000c994047310022610540c0008934047250096495cc0900238f40471d00023900007002385004708008e0c011c1002381001101008e00, 0x3aae40115a80e6b101d52403aa455b04800228d01d514038a2421044021e71008cda0089a40752a80ea52007ca20001400152700223e00ac7403a8500750800ea0c01d4100088180750200ea00, 0x8a7c0114d802297004526008a3c117458022870445060089dc2703a80227309c0e40899bc1173582266701acc600895c1172980224f044496ba81281151f82263b004426bc00480110884e01000441ebb80380110684e00c004416bb00280110484e00800440e9200181170284e0040044061b80081110084e000, 0x11628022c100457a008a740114d00229909c130008a54011490022760044ea1381d001139023a6e045cd405c998041310236520464940088500110800220e00441800882001102002200, 0x458a008b040114e80229a0045321382600114a8022920044ec0089d42703a0022720044dc08b9a801133023e620444940088500110800220e00441800882001102002200, 0x404e002202, 0x4594008b25790640022c5004584008ae8069590022ae00453a008a680114a802292001514023a180113b02366a0034c40069280110a00221000441800882001102002200, 0x11568022a95dc138008a14011408022650044c200f93401f24802a3d0004720088500110800220c00441000881001101002200, 0x22ce00459a000330011650022c600458a000310011610022be00457a0002f00115d00eab6001564002ab806b5500229e00453abc827001d410036620034940088580110a00221000441800882001102002200, 0x459a008b28011648000c8004584008ae801f590022ae00453c008a680114b00229200451c00fa2801143018e82007cd40088500110900221000441800882001102002200, 0x141980283117804e002202, 0x11628242c1007552008a7401b4c823292044522ba82400114280e276005ce400a9b8071350002660004ca0001900013100ee4d004c720008500010800220e00041800082000102000200, 0x458a00fb0401f5880229d007d3208da480114680e2760084e400f9b801f3680006c007cd400a99807131004655004c7400f85001f0800220e007c1800f82001f02003e00, 0x115e8022b95d8130008a54011488022750044e200f9580112900024e0044940088500110800220c00441400882001102002200, 0x8b38011668000cc004594008b18011610022be004574008ad801f590022ae048554008a780114b003e8a0075040088580110a00221000441800882001102002200, 0x22c200457a008ae80115c8000b8004534008a54011490022910001200089d4011390022710000e000895801f290022515ec0a0008938001250022495e80900088500110800220c00441400882001102002200, 0x404c002202, 0x5e01900283000504c002202, 0x196700bab201ed627f02c0011568032aa0065520882a00114280328201c502be82000a53500ee692580d000c994019310022610680c0008934019250042495f009000c8f40191d00023900007000c8500190800320c00641000c81001101003200, 0x83ae807f5cace0b800456a03fac8073588440b001fd22008a3407144804271008cda0089a407f2a80fe52007ca20001400332700223e00ac7403f85007f0800fe0c01fc1000881807f0200fe00, 0x8a7c0114d8022970a012a008a4c28049024a8f049d1600ca1c06d418022770044e60089bc12735802267006cc600895c1272980224f048c96bf01280151f824a3b004426c080480110885001000441ec000380110685000c004416bf80280110485000800440e928018127028500040044061c000812300850000, 0x11628022c20045821403000115e8022ba00453a008a640114a8022760044ea1401d00113902126e049cd40669980173100425204a4940088500110800220e00441800882001102002200, 0x459a008b28011648500c800457a008ae80114f00229a00452c008a542804a00229200451c093a2801143025682048c940088500110900221000441800882001102002200, 0x101980203118004e002202, 0x4594008b25790640022c5004584008af40115d000ab200655c008a740114d002292019514008a180113b00426a003cc40079280110a00221000441800882001102002200, 0x4592008b1401160803eb200453a008a680114c80009800452400fa28011430022760044e40089b801f35002266034cc40088500110800220e00441800882001102002200, 0x5062002202, 0x1810620022ad004552008a14011408022650044c200f93401f2480663d0004720088500110800220c00441000881001101002200, 0x1162803ac104a574091ae57e05c0022ad00453a00da6401b40803276005ce400a9b8073350002660004ca0001900013100324d004c720008500010800220e00041800082000102000200, 0x458a00fb040215d0022b500453a00fa6401f4480e6760084e400f9b801f3680006c007cd400a99807331004655004c7400f85001f0800220e007c1800f82001f02003e00, 0x17f0600022bd004572008a54011488022750044e200f9580112900024e0044940088500110800220c00441400882001102002200, 0x8b34011648022c500453c008a740004e00229a00452c008a4801147003e8a00450c00da080113b003e6a006cc40088500110900221000441800882001102002200, 0x6001900203000404c002202, 0x504c002202, 0x2829005050002202, 0x200d004018002202, 0x100a80201318201e002202, 0x6080a00201200401c000206, 0x100e802019183026002202, 0x3080a860c0d00201800401c003e06, 0x1013802021185032002202, 0x30c0a86141100202000401c002206, 0x101980202b187042002202, 0x61c1600202a00401c002206, 0x2029004050002202, 0x16f0090520104a801c1480303b00505200801400c14801004001052000, 0x2206, 0x456a008ac4011468022890045020089b401134803e550044a20008f80111e80003c0044740088500110800220c00441000881801102002200, 0x455a096aa401146802285006d0200c99406130802a4d0084920008f40011d0002390000700008500010800020c00041000081001101000200, 0x457a008ae40114a8022910045120089d401138803e560044aa0001500112900024e0044940088500110800220c00441400882001102002200, 0x8ab401f55003ea9620150008a5401142803e81029cca01098401329003e4d007c9400f92400024002a3d04bc7200f85001f08003e0c007c1000f81001101003e00, 0x458a008b040114e8022990045220089d80113a8000740044e400f9b8011350002660044c40088500110800220e00441800882001102002200, 0x8ab4011550022a9624150008a7401142802281005cd4008994011310022610000c00539340212480323d04bc720088500110800220c00441000881001101002200, 0x40660080c40101780202d004056002202, 0x40540080800100c00201200401c002206, 0x8b38011668000cc004594008b18011610022be00457400fad8011590002ae004554008a6801149003e8a00450c0088580110a00221000441800882001102002200, 0x22ce007564008ab4011550022a9000150008a14011408022650044c200893401f2480223d0074720088500110800220c00441000881001101002200, 0x4066002202, 0x4064002202, 0x2202, 0x459c008b358c066003ab201ed628102c0011568022aa0045520b02a001b4500f289328110008a140114100228106c1000089940113100226162c0c000893401125003e496280900088f40111d0002390000700088500110800220c00441000881001101002200, 0x22b900456a008ac40114880228d0045120089b4011348022550044a400f9440002800223e004c740088500110800220c00441000881801102002200, 0x22c100457a008ae40114c8022950045220089d4011390022710000e000895801f2900224e005c940088500110800220c00441400882001102002200, 0x114f85409d0045361502680114b8022935e4124008a3c01f45aba08a00450ec6021801b418022770044e60089bc01f358022670004c6c681880232ba7c05300649e02192c0151f805a3b004426c780480110885401000441ec700380110685400c004416b800280110485400800440e95801801f028540040044061e000800100854000, 0x8b34011650022c90a8190008b14011610022ba007d64008ab80114f00229d0a8138008a680114b00229200451c00fa28011430036820004c40088500110900221000441800882001102002200, 0x8b34011650022c90a8190008b14011610022ba007d64008ab80114f00229d0a8138008a680114b00229200451c00fa2801143003a820004c40088500110900221000441800882001102002200, 0x5066002202, 0x18f0660022ad004552008a14011408022650044c200f93401124805e3d0044720088500110800220c00441000881001101002200, 0x1670022cd04c19800eb24001610002c1634180007ae800b590002ae00455a8f82b00114f00029d06013800da680194b006e9200551c011a2800143000285000108000a0800d3900126a0004cc008994ea0321380491a80720008500110900021000041800082000102000200, 0x22cd007d92010ae80115a80229e007d34011a5802149003e8e007d1a00023001f45002a86008d0408d9c801136804251004c7400f85001109003e10007c1800f82001f02003e00, 0x22cd004592008af40615900229e004534008a580114a80009400452401ba380214500328600dd040089d40ef3500c252005c940088500110900221000441800882001102002200, 0x18e0640022ad004552008a14011408022650044c200f9340112480023d0044720088500110800220c00441000881001101002200, 0x5064002202, 0x280d005018002202, 0x140a80281319001e002202, 0x6400a00281200501c000206, 0x140e802819191026002202, 0x3240a86440d00281800501c003e06, 0x1413802821193032002202, 0x3280a864c1100282000501c002206, 0x141980282b195042002202, 0x6541600282a00501c002206, 0x456a008ac40115480228d0045120089b401134803e550044a20008f80111e80003c0044740088500110800220c00441000881801102002200, 0x456a008ab401d54802285006d0200c99413130802a4d004c920008f40011d0002390000700008500010800020c00041000081001101000200, 0x457a008ae4011588022950045220089d401138803e560044aa0001500112900024e0044940088500110800220c00441400882001102002200, 0x8af401156803ea900450a00fa0801f40b2c0800344ca01798402529003e4d007c9400f92400024002a3d001c7200f85001f08003e0c007c1000f81001101003e00, 0x458a008b040115c80229d0045320089d80113a8000740044e400f9b8011350002660044c40088500110800220e00441800882001102002200, 0x8b14011568022a900450a008a0801140b2e08000f4d4008994011310022610000c00689340212480323d001c720088500110800220c00441000881001101002200, 0x8b34011648022c100453c008a740004e00229a00452c008a4801f4700228a00050c008a0801139003e6a0044cc0088500110900221000441800882001102002200, 0x22cd00455a008aa401b45002285004504008a04000400022650044c200893401f2480223d006c720088500110800220c00441000881001101002200, 0x506600a0c40141780282d005056002202, 0x505400a0800140c00281200501c002206],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000, 0x59e000b2c00163801ec300057e005aec001578160ad0005560502a40014f801a9b00052e004a4c001438120850005060402040073b8006730014ce0381940073180c06100149e0281340032580804900046e0080d80101a8000340004660080c80101880003000042e1380580010a8020140004261300480010880201000041e1280380070680200c0004161200280030480200800040601800800100802000, 0x11413e22026c4004b87e0930ec11e1d022c320438620830f80ee1e81cc3903787006b0c00ce17818c3702b86c0530b809e16812c2c01f85603b1200262380484600880401010c01e2100384100680400c00c0160000283c0048040080d400e1a0018330028040040a800614800828000804000, 0x11678022cb00458e2f0314011618ba0c100457e008aec0115b803eb300455e2a02b401d558a60a900453e2e02740114d8b609900452e008a4c01147803e8b00450e29021401b418a20810044ee2d01d8011398b2072007cde2b81b801f358ac06a0044ce278198500328022631340c42701840232b80425300649e2601340172589604900547e2500f40131d89203900442e3000580110a8060140044262f80480110880601000041e0080380110680600c0044162c00280110480600800440e2a801801f028060040044061e000800100806000, 0x39033c02d658026c7004d86009afc6f05e8026bb1b8172009adc013598d00b1004d5e015aac0134f80529b00a52e368254013498d809100a51e014a2c67044805287009d060099dc6b03a8026731a80e20099bc013358cc069004cce00198c640308026570300ac0201540002a0026530100a400193c0102700804d00009800992c04025004a3f18807c3180f46101e00263b00942e3980580130a808014004c2638804802908808010004c1e3800380130680800c004c1634802801304808008000c0e32801801302808004004c0624800800300808000, 0x2acf00559600ab1c02f61802abf00557600aadc03559802aaf1fc15a00aaac7d0550fc0a91f015000aa7c0394d802a97005526019a3c03145802a871ec10a00aa0c790410f40811e010001b9dc02f39805e6f005cd600a99c4f032805e631d80c43b818475030002a570094a6310148630288c205000549e0281340152580a04a0300920001200151f80a03d0014760280e80101c80003800542e4180580150a80a01400ec264100480150880a01000541e40803802f0680a00c00dc164000280150480a00800540e2500180050280a0040054063a00080150080a000, 0x49833c04365802ec724418a00bb0c90060802ebf005d764602e40175b802eb3005d5e003aac0414f91e09d005d364702640414b80829322c12200ba3c0414580828700fd0600b9dc1503b00c0750000e800b9cc06039002e6f2240dc00b9ac6a035000e670040cc03019400032002e630180c400b95c0172991005200f49e4281388602690804c005c9600b8fc0031d8c803900f42e4a00580170a80c014005c264900480410880c010005c1e4680380170680c00c001c164500280170480c008005c0e4380180170280c004005c062580080070080c000, 0x32cf00659600cb1c019618032bf00857600cadc049598032af28015a00caac9e05513e0a927415000ca7c0194d803297012d26023a3c0454580328727010a00ca0c9a0411360812641000119dc0213980326f00f4d64281a8860349080680064ce0381940193180e0620540c200018002f2b80265300649e2781340212592e04a2600924b01200191f80e03d0014760380e80101c80003800642e5200580190a80e0140134265180480190880e010008c1e5100380190680e00c0064165080280210480e00800640e2600180050280e0040064064a80080190080e000, 0x6d9e598338b40669640cc006d9658832401b638036c32bc18200dafc01b5d8036b7013d6600dabc0015580369f07013c0402740004e00369b02013400da5cad04b003693238124027a3caa04700368b1b0114000a1c0104301008500010800da0c08041003677006ce65601c801b37809e6b2a40d400d99ca603314e0652940c800d98c0532b80a25301149e01f92c0311f804e3b006c2e5a805801b0a81001401542658004801b0881001000041e57003801b0681000c006c1655802801b04810008006c0e54001804f02810004006c0628800800100810000, 0x11679880cd004596008b1c011618022bf007d76008adc01d598022af30015a008aacbe05517e0a92f4150008a7c0114d802297007d26008a3c01b4594c08a29c112528220011438120850045060482081c040800080015cee0259cc0473780826b0044ce4e0194011319760622f00c25d01800332b80525300449e3d813401f2597004a2e40925b81200111f81203d0004760480e80101c80003800442e6280580110a8120140044266180480110881201000441e6100380110681200c00441660802801f0481200800440e290018001028120040044065b000801100812000, 0x759e1083380a0668000cc00759605032801d639a40c634c18a68831001d619620c200757e6702f801d5d9200ba01656e6582d801d598dc0b200055e0082b80a0568000ac0075560502a801d4f803a9b34013400ea5c01d4999a09200751e02ca2cca045003a8731c10c640214c6042003a830074ee00e9cc01d3780b26b0074ce00098c05d2b80b65301249e00392c0351f80563b017c2e6a805801d0a8140140004266a004801d0881401000741e67803801d0681400c00741666002801d0481400800740e6480180590281400400740629800800100814000, 0x11679c60ce004596008b1c011618022bf007d76008adc01d5998e0b23201626302c0011578160ad0045560582a8210548000a800453e008a6c0114b803e9300451e00da2c011439800850045066f0208df0409ba080008cee0109cc01937802e6b0044ce500194011319b60623700c26d01800152b80265300449e3f813401f259b004a3640926b81200111f81603d0004760580e80101c80003800442e7200580110a8160140044267100480110881601000441e7080380110681600c00441670002801f0481600800440e2a0018001028160040044066b000801100816000, 0x7d9e00fb2c01f638042c3007d6e0a02d401f598260b1007d5e02caac01f4f80969b007d1e09023401f45822089007d0e027a0c0373782006d0084d60781a402133802e63007c8e0601180c022800044007c860601080c02080004000547e0280f80131d80803a007c2e73805801f0a818014007c2673004801f08818010007c1e7280380210681800c007c0e07001801f02818004007c0614000800300818000, 0x3f013e7d826cf704b9ec0933c811e78822ce00439920833d40ee7a01ccf00379de06b3040ce54018cee02b9da0533a409e74012ca101f90e03b3fc0267f0048fd00881a0103e801e7c8038f800681a00c038016000028f300481a0083b000e758018ea00281a0041540061480082400081a000, 0x11678022cb00458e88031401161a1e0c100457e008aec0115ba120b5007d668402c401157803aab00453e8702740114da1a09900452e008a4c01147a0e08d007d16830224011438036830044ee8601d801139a160720044de2781b90503680226b1340d48201a400133a0206600dcc68001880232ba060550084a681014401927802e4b00dc7e4000f80031d8ca03a00442e8900580110a81c0140044268880480110881c010007c1e0600380110681c00c0044168500280110481c00800440e79801801f0281c0040044061500080010081c000, 0x23e0cf478196010b1d1c0628042c346c182010afc0215d8042b7008566010abc05b5580969f46813a025a6d1904c804297012d26030a3c04b458096870145060109dc1503b01e0750000e80109cc0f03900426f0300dc0781b40003600426b03c0d401799d130330026631a80c401095d1502b22c0554500a801094c02127802e4b2200940178fc0131d8cc03a00bc2e9000580210a81e0140084268e804804b0881e01000841e8c00380210681e00c0084168b80280210481e00800840e8100180210281e0040084061580080030081e000, 0x46cf008d96011b1c02361806ebf00dd76011adc05d598046af4b015a011aad2a0552560a94a4150011a7c0234d806e9700dd2602ba3c053458046874a010a011a0d2604124e0814941000119dc02139a2a0724580e28a01c002337802e6b008cce080194023318200620540c20001800372b802653008c9e0801340372582004a0300920001200231f89e03d001c769180e92401ca44038015c2e9780580230a820014008c2697004802308820010008c1e9680380230682000c008c1681802803704820008008c0e16001800702820004008c0690800802300820000, 0xfb3d3b066803ecb4e819200fb1d38062803ec3007d7e032aec01f5b803eb3007d5e02caac01f4f83809e04413a00027001f4d82209a012d2e9b025804b49a32092007d1e0602381104680008c007d1608822803343a60086018d0636020801f3b8096734d40e400f9bd3203726606d4c40d800f9ac01f33809e632a40c401b95c04b2980964f01049600a8fc0291d8ce03a007c2e9e005801f0a822014007c269c804801f08822010007c1e9b803801f0682200c007c169a002804b04822008007c0e83001801f02822004007c0617800800900822000, 0x8b3c011658022c7004586008afc01f5d8022b750416a008acd400588022af007556008a7c0114d802297007d2699024933048a6209000451e0902340114582408a0701120002200114380368300dcee0309cc01137a5006d0044d69f81a401933802e630044ae09015401f298240520300a20001400152780524b00447e3d80f80011da7a03a00442ea200580110a824014004426a180480110882401000441ea100380110682400c00441683802801f0482400800440e9f00180110282400400440618000800100824000, 0xfb3c210670260cd00019800fb2c13065003ec753818c00fb0d3a0610042bf52c17c010aed1b05d003eb703016c0982d40005a003eb304c16400aabd4505700ceab1b815400fa7d4d04f003e9b007d2e010a4d4a049003e8f51c11ca4023546046003e8b007d0e02ca0cca041003e7701a4e600f9bc01f35803e67013cc601b95c0212980424f005c9600a8fc0131d8d003a007c2ea8005801f0a826014007c26a7804801f08826010007c1ea6003801f0682600c007c16a4802802104826008007c0e84001801f02826004007c0618800800b00826000, 0x8b3c011658022c7004586008afc01f5da8e0ba520172a302e00115b8280b50045660a02c8210588000b000455e00eaac0114f80229b00452e00fa4c01147a8208d004516aa02240114380368300dcee0109cc01137a5806d0044d6a981a401933802e630044ae0a015401f298280520300a20001400152780264b00447e3f80f80011daa203a00442eab80580110a828014004426ab00480110882801000441eaa80380110682800c00441684802801f0482800800440ea900180110282800400440619000800100828000, 0x459e008b2c0115f8360bd0045760d02e40115b8042b300455e00eaac0114b8320950045260c02440114780968b00450e00da0c0112f82a05e0540ba0001700112d82a05a0540b20001600232b8200560084a60781480192780e04e005c9603012802f1f80263b00442eac80580110a82a014004426ac00480110882a0100044160b80280110482a00800440e7500180210282a0040044061980080070082a000, 0x59c13eb3026d6204bac209355411ea4822ce10439980835800eeaf81cd42037a6806b3080ce55818d5d02bab805356c09ead012c8101f8e003b5a8026b480496800882c01059401eb200396300682c00c05c0160000295e00482c00842800e758018e500282c0041600061a00082500082c000, 0x11678022cb00458ebc031401161aee0c100457eba02f40115dae60b900456e00facc01157803aab00453ebb02740114daea09900452eb9025401149ae209100451e00fa2c011438036830044eeb801d84f03a8022735bc0e42681c402337a5a06e0084d68b81a802333944066001cc645018801f2badc056008ca6b6814800127ad804e008c96b581280151f80263b00442ebd00580110a82e014004426bc80480110882e01000441eaf00380110682e00c0044160a80280110482e00800440e76001801f0282e0040044061a80080010082e000, 0x8b3d840668022cb60c192008b1d810628022c300457e008aec0115b80d2b300455e00eaac0114f83809e06013a0002700114d83009a00452e0a82581804a8000940045260c024804b47af808e012d168c822804743af608601ad064702080113bafc0765fc0eabe81d00113980226f012cd69a81a8011338036632b00c401195c04b2980324f0104964581280391f80523b00442ec280580110a830014004426c100480110883001000441ec000380110683000c004416ba80280110483000800440e77801804b028300040044061c000800d00830000, 0x8b3c011658022c7004586008afd8a05e8022bb624172008adc01f598022af007556008a7c0114dafc09a5fc132be82600114b8320950045260c82481c04880009000451e00fa2c011438036830044ee0c81d4011398320720540e20001c00233780426b0064ce02098c0112ba50056007ca6c381480112793804e000496c301280151f80263b00442ec600580110a832014004426c580480110883201000441ebb00380110683200c004416c400280110483200800440e78001801f028320040044061c800800100832000, 0x8b3c210670340cd000198008b2c1a0650022c765018c008b0d830610022bf05417c0d02f40005e0022bb068174010add8e05b0042b346c16400cabd8d05700daab240154008a7d9304f00229b00452ec802599104ab1e094004526008a3c02145a9408a00450e00ea0ccd0410022770044e60089bc06535802267006cc601195c0212980324f005c9646012802f1f80263b00442ecb00580110a834014004426ca80480110883401000441ec900380110683400c004416bb80280110483400800440e788018021028340040044061d000800f00834000, 0x8b3c011658022c7004586c8030991060b1e0c000457e0d82f40115d8360ba0841720002e00115b803eb300455e00eaac0114f80229b00452ec5025401149b3409100451e00fa2c011438036830044ee0d81d4011398360720540e20001c00233780426b0064ce00b98c0112ba58056007ca6cc01480112794004e000496cb81280151f80263b00442ece00580110a836014004426cd80480110883601000441ebc00380110683600c004416cc80280110483600800440e79001801f028360040044061d800800100836000, 0x458e1003140116183e0c100457e008aec0115b803eb300455e00eaac0113f83807e0700fa0001f00113d83807a0700f20001e00113b8320760044e60c01c80113782406e007cd60881a801133812066006cc60401880232b80965300649e02092c0151f80523b00442ece80580110a83801400441e0f00380110683800c004416b180280110483800800440e7c001801f0283800400440620800800100838000, 0x66c13ec9026d5604ba9809338811e67822da6043b4a0834b80ee8e81cca303792406b6900ced1818c8202b8e205368809ed0812da001fb3e03b6a4026d40049a700883a0105e401eb200395800683a00c4440167c8028e600483a00817c00e2100182600283a0040780060000099e00083a000, 0x1167b6a0cd004596da0324011638022c300457e00faec0115b803ab300455ed982b401155b640a900453ec582780114db0009a00452ea1825801f49a6e09200451e6182380014595c08a00450ed882184f0428022836c01042682040233b8042730134de00b9ac01133b5e0650044c6d7018403b2b802653007c9ed6813401125b5804900047ed580f40111db5403900442edb00580110a83c014004426cf00480110883c01000441eb280380110683c00c0044167d002801f0483c00800440e2180180010283c0040044060e00080110083c000, 0x22cf08419c0f8334000660022cb07c194008b1c1c06303e0c5000188008b0c1f0610022bf6e417c008aed8305d0022b76e016c00facd3a0590022af6dc15c00daacb105500229f6ec13cde0275ba04e00229b00452e008a4c01147803e8b00450e00ea0cd00410022770044e60089bc01f35802267006cc65781880232ba3c05300649e02192c0151f805a3b00442edf00580110a83e014004426de80480110883e01000441eda00380110683e00c004416b300280110483e00800440e7d801801f0283e0040044062200080010083e000, 0x22cf004596dd8329bc064b740c800458e100314011618400c20841820003000115f8022bb64c174008adc01f59a9a0b200455e7182b801d5580229f08013a008a6c2004d038099000130008a5c01149b0209200451e00fa2d3804500228731010c00da0c0113bb140760044e6e081c801137a8206e007cd6e001a8011339800660004c6df81880232ba3e05300649e49812c0151f8e403b00442ee180580110a840014004426da80480110884001000441ee100380110684000c004416b380280110484000800440e7e001801f0284000400440622800800100840000, 0x454e108298210528000a4004546108288210508000a000453e1002780114d83e09a00452e0d82580114983409200451e0a023801f4582608a00450e05821801d418140820044ee0089cc01137803e6b0044ce00d98c0232b80425300649e00b92c0151f80263b0044261180480110884201000441ed380380110684200c004416b400280110484200800440e7e801801f0284200400440623000800100842000, 0x63013ec2826d4404ba7809331411e5a822dcc043b960834bc0ee9001cca403792806b7280cee4818c8302b8e605372009ee3812dc601fb8a03b6d8026d400499d0088440105e801eb480395900684400c4480167f0028e700484400818000e2380182700284400408c006000009c4000844000, 0x1167b860ce004596de832801163b380c6004586ca83080115faae0be007d76a782e80115b9c80b60005666a02c801157bac0ae13c15a008aadd505509a0a900453e008a6c0114b803e9300451e00da2c01143ba8085004506e982040573b805e730064de01e9ac01133ba40650044c6e881840152b804a53007c9ee8013401125b9e04900047ee700f40111db9a03900442ee200580110a846014004426d480480110884601000441eb500380110684600c0044167f802801f0484600800440e2400180010284600400440610800801100846000],
  [0x8013e0f826c1b04b83409305011e09822c0b0438140830640ee0c01cc1203782206b0240ce04018c1002b81e05301c09e03012c0501f80803b08c0261100482100880001007801e0e80381c00680000c05c0160b00281500480000803800e0680180c00280000400c00601000801000800000]]

def witT6 : List ℕ := [0x18040001a0641e, 0x40090001c06c24, 0x1804058270901e, 0x58100001b06424, 0x3004058270901e, 0x4c04058270901e, 0x2406058270901e, 0x4006058270901e, 0x10000181e06819, 0x2400040240641b, 0x18000241e06c1a, 0x300004c270681b, 0x10000301e06c19, 0x24000301e06819, 0x400004c1e06819, 0x18000101e0641a, 0x2000040240641b, 0x10000582406c19, 0x2400040240701b, 0x580c0001c06827, 0x4000024240641c, 0x58130001b06827, 0x580c0242407827, 0x2000040240701b, 0x30000241e06c1a, 0x18000401e0701a, 0x4c000401e0701a, 0x18000582706c1a, 0x3c000242406c1c, 0x18000242306c1a, 0x300004c270701b, 0x58090001c06424, 0x4c00030270681c, 0x58090302707824, 0x24000301e06c19, 0x100004c1e07019, 0x400004c1e07019, 0x3c00024240641c, 0x10000302306c19, 0x30000241e0641a, 0x5800024240641c, 0x24000582406c19, 0x24000302306819, 0x10000582407019, 0x4c000401e0641a, 0x5800040240641b, 0x40000582406c19, 0x400004c2a06819, 0x200004c270681b, 0x30000101e0641a, 0x400c058270901e, 0x4c000101e0641a, 0x4c09058270901e, 0x24000181e06819, 0x40000181e06819, 0x10040241b06419, 0x10000301e06819, 0x100004c1e06819, 0x18000241e0641a, 0x301b06419, 0x24000001906419, 0x40000001906419, 0x10000582706c1a, 0x18000401e0641a, 0x241b0681a, 0x241b06419, 0x18060241b06c1a, 0x24090241b06419, 0x40100241b06c19, 0x241b06c19, 0x401c06419, 0x1800058270901e, 0x10040401c06419, 0x1800024230641a, 0x10040301b06c19, 0x301b0681a, 0x30040301b06419, 0x301b06c19, 0x4c1c06419, 0x18040301b06419, 0x18060301b0681a, 0x300004c240681b, 0x1000058270901e, 0x10000302306819, 0x24090001a06819, 0x24090001b06c19, 0x24090301a06819, 0x301a06419, 0x3000058270701a, 0x18000101e06c1a, 0x24090301e06819, 0x24000582407019, 0x10000181e06c19, 0x24000201e06c19, 0x10000201e06c19, 0x40100001a06819, 0x40100001b06c19, 0x401004c1a06819, 0x4c1a06419, 0x4c000582706c1a, 0x18000101e0701a, 0x401004c1e06819, 0x10000181e07019, 0x400003c1e07019, 0x100004c2a06819, 0x30000582706c1a, 0x10000582406c1a, 0x10000582706c19, 0x300004c240641b, 0x30090001a0641e, 0x4c100001a0641e, 0x100004c2a07019, 0x3c00030270681c, 0x301e07819, 0x30000181e06819, 0x10000301e06419, 0x18000301e0681a, 0x10040301e06419, 0x4c100001b06827, 0x100004c270681b, 0x100004c2706819, 0x20000301e06419, 0x1800040240641a, 0x240004c1e06819, 0x4c1e07819, 0x4c000181e06819, 0x100004c1e06419, 0x100404c1e06419, 0x4c090001b06827, 0x10000302706819, 0x3c0004c1e06419, 0x1800024270641a, 0x10000302406819, 0x1800024240641a, 0x40100401c06419, 0x200004c270641b, 0x241e07819, 0x10000241e06419, 0x18000241e0681a, 0x10040241e06419, 0x4c100001b06424, 0x1800040240641b, 0x100004c2406819, 0x24000201e06819, 0x40000301e06819, 0x401e07819, 0x10000401e06419, 0x10040401e06419, 0x400c0001b06424, 0x400003c1e06819, 0x40000301e06c19, 0x30090001a06423, 0x3000040240701b, 0x24000402407019, 0x40000242406c19, 0x300004c270701a, 0x4c000302706c1a, 0x24000001b06c1b, 0x18060241b06c19, 0x24060241b06419, 0x40100241b06819, 0x24090401c07019, 0x18000582706c19, 0x18040582709019, 0x401c0681a, 0x3004058270641e, 0x4c04058270641e, 0x580c0101e06427, 0x40090001c06c19, 0x30000001b06c1b, 0x4c040301b06819, 0x2400040240641a, 0x4000024240641a, 0x300c0301b0681a, 0x4c130301b06c1a, 0x100404c1c07019, 0x2406058240681e, 0x4006058240681e, 0x58090181e06824, 0x30000001a0681a, 0x1800058270701a, 0x5800010240641c, 0x10040581c07019, 0x580404c1e06819, 0x4c000001a0681a, 0x5800010240641b, 0x10040581b06c19, 0x58040301e06819, 0x10000581e06c19, 0x24090301e07819, 0x40090301e06419, 0x3009040270901e, 0x300904c270901e, 0x401004c1e07819, 0x4c10024270901e, 0x4c10030270901e, 0x10000242406c19, 0x18000302706c1a, 0x10000402407019, 0x180004c270701a]

def S6 (s i : ℕ) : List ℕ := unpackW wdT6 9 ((levT6.getD s []).getD i 0)

def N6 (s : ℕ) : ℕ := (levT6.getD s []).length

def A6 (s i tag : ℕ) : ℕ := findAct 4096 ((actT6.getD s []).getD i 0) tag

def W6 (w : ℕ) : ℕ := witT6.getD w 0

def Z6 (s : ℕ) := barrier 25 S6 N6 A6 W6 idRot s

theorem enc_inputs6 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT6) = xsT6 := by decide +kernel

theorem enc_goal6 : encL fT6 rowsT6 = goal 25 := by decide +kernel

theorem mask6 : mask 25 = 2 ^ rowsT6.length - 1 := by decide +kernel

theorem proper_fail6 : ∀ zs ∈ xsT6.sublists, zs ≠ xsT6 → (cov 25 zs &&& lo 25) ≠ lo 25 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked6 : ∀ s ≤ 8, ∀ i < N6 s, Z6 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun6 (s : ℕ) (hs : s ≤ 8) (h : NatRun (mask 25) (goal 25) s xsT6) : False := by
  have hc : NatRun (mask 25) (goal 25) 8 xsT6 := extend_run h hs
  have p : xsT6.Perm (S6 8 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked6 8 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub6 : ∀ s ≤ 8, ∀ zs : List ℕ, zs.Sublist xsT6 → NatRun (mask 25) (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT6
  · subst e; exact noRun6 s hs h
  · exact proper_fail6 zs (List.mem_sublists.2 hz) e (required h)

theorem low6 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT6 8 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT6 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 8 h
  have hr : NatRun (mask 25) (encL fT6 rowsT6) s' (ws.map fun a => encL a rowsT6) :=
    Run.map (fun a : BFn 5 => encL a rowsT6)
      (fun a => by rw [mask6]; exact encL_inv a rowsT6)
      (fun a b => encL_and a b rowsT6) (fun a b => encL_or a b rowsT6) hrun
  rw [enc_goal6] at hr
  refine no_sub6 s' (by omega) _ ?_ hr
  rw [← enc_inputs6]
  exact hsub.map _

def mono6 : List Gate := [⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [11, 12]⟩]

theorem mono_ok6 : ∀ g ∈ mono6, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono6, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval6 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono6, 13⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve6 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeae8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono6, 13, mono_ok6, ?_, mono_eval6⟩
  by_contra hlt
  have hlen : mono6.length = 9 := rfl
  apply low6
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 8
    omega

def rowsT7 : List ℕ := [1, 1, 1, 2, 2, 2, 4, 4, 8, 9, 9, 9, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 5, 17, 3, 6, 10, 5, 6, 10, 11, 13, 25, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT7 : List ℕ := [0x933c9e000e07, 0x12e4772070038, 0x274e9a43870c0, 0x3c8fe41c07f00, 0x3ff9009ff8000]

abbrev fT7 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT7 : List ℕ := [0x2884007fc7, 0x6ff6007fff, 0x20412000000, 0x102884000000, 0x2401203f80f8, 0x244120000000, 0x3701be3f80ff, 0x803c00000e00, 0x931008000000, 0x933c9e000e07, 0xb73dbe3f8eff, 0xb77dbe000e07, 0x1084640000000, 0x12e0000070000, 0x12e4772070038, 0x12e6ff6077fff, 0x13e6ff6070038, 0x18b165bc78f3f, 0x19b7ede000e07, 0x1bf577a070038, 0x1bf7ffe070e3f, 0x240e800007000, 0x2748000380000, 0x274e9a43870c0, 0x276edb63870c0, 0x2d19009f88000, 0x2d1b88df8ffc7, 0x2f79008380000, 0x2f7f9ac3870c0, 0x2f7fdbe387ec7, 0x348c241c07100, 0x348ee40007000, 0x36cc361fff1f8, 0x37cefe43870c0, 0x37eeff63f70f8, 0x3c89001c00000, 0x3c8d641c00000, 0x3c8fe41c07f00, 0x3cafe53c07f00, 0x3d8fec5c07f00, 0x3db9009c00000, 0x3dbd65bc00000, 0x3dbfe49c07f00, 0x3dbfedfc07f07, 0x3ecff61c07f00, 0x3eeff73c77f38, 0x3fcffe5f87fc0, 0x3ff9009ff8000, 0x3ff941bff8000, 0x3ffb88dff8000, 0x3ffbc9fff8e07, 0x3ffd129ff8000, 0x3ffd649ff8000, 0x3ffd77bff8038, 0x3fff9adfff0c0, 0x3fffe49ffff00]

def levT7 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x2a06015],
  [0xc02606415, 0xd82c06015, 0xc02607811, 0xa81803c0a, 0xc02608c0c],
  [0x300981803c0a, 0x30098210600f, 0x300b01803c0a, 0x300981b0600a, 0x360981803c0a, 0x300981203c0a, 0x300600f02807, 0x260600f02802, 0x300982106c18, 0x36098210600f, 0x30098210480f, 0x300841f0600f, 0x300841803c07, 0x260841803c02, 0x300b0210600f, 0x3007c1803c0a, 0x300981805403, 0x300b0180540f, 0x36098180540a, 0x300981903c0a, 0x3009c1803c0a, 0x310981803c0a, 0x300981e03c04, 0x260701803c0a, 0x30098180440a, 0x300a01803c0a, 0x320981803c0a, 0x300b01b0600a, 0x360b01803c0a, 0x300b01203c0a, 0x300600f02805, 0x2c0a41803c0a, 0x2c0600f02802, 0x300b01803c08, 0x290981803c0a, 0x330981803c09, 0x30098180500a, 0x300981d03c0a, 0x300ac1803c0a, 0x300981b0480a, 0x2606c1a0600a, 0x3006c1802807, 0x2606c1802802, 0x360981b0600a, 0x260681803c0a, 0x300982302806, 0x300801803c0a, 0x300981803c0c, 0x300b41803c0a, 0x340981803c0a, 0x300b8180340a, 0x300981804c0f, 0x300982203c0a, 0x350981803c0a, 0x360981203c0a, 0x360600f02807, 0x360941803c0a, 0x260600f02801, 0x36098180380a, 0x300941803c0a, 0x300480f02807, 0x260480f02802, 0x300bc1603c0a, 0x370981703c0a, 0x300600f02c0a, 0x1803c0a01c02, 0x380901803c0a, 0x260601003c0a],
  [0x300981803c0a, 0xc0260600f0280a, 0x30098210600f, 0xc0260841803c0a, 0xc0260601503c0a, 0xc0260600f02803, 0xc0260781803c0a, 0xc0260600f02804, 0x300b01803c0a, 0xc02c0981803c0a, 0xc0260600f02808, 0xcc300981803c0a, 0xc0260600f02809, 0xc0260600f03c0a, 0x300981b0600a, 0xc02606c1803c0a, 0xc02608c1803c0a, 0xc0260600f02806, 0xc02e0981803c0a, 0xc0260600f0340a, 0x360981803c0a, 0xd8300981803c0a, 0xc0260600f0380a, 0xc0260601803c0a, 0x300981203c0a, 0xc0260601203c0a, 0xc02f0981803c0a, 0xc0260601603c0a, 0xdc300981803c0a, 0xc0260601703c0a, 0xc0260981803c0a, 0x300600f02807, 0xc0260600f02807, 0xe0300981803c0a, 0xc0260901803c0a, 0xc0300981803c0a, 0x260600f02802, 0xc0260600f02802],
  [0x300981803c0a]]

def actT7 : List (List ℕ) :=
  [[],
  [],
  [],
  [0x4082008102010200],
  [0x6c1800d82001b02003600, 0x329d807d3a8000740194180328200650200ca00, 0x2d3700d66200b41801682002d02005a00, 0x3f8e80311c80003800c41801882003102006200, 0x472b00e64a011c1802382004702008e00],
  [0x8a2800d31000610000c1800182000302000600, 0x60a, 0xd4f001a8a0034ca00698800d1c801a1000341800682000d02001a00, 0x60a, 0x114e80228d0045140069880191d00221000441800882001102002200, 0x60a, 0x602, 0x602, 0x0, 0x220a, 0x0, 0x60e, 0x0, 0x0, 0x1a0a, 0x8a2800d31000610000c1800182000302000600, 0x1750402d9880592500364900009000d8f401b1d003610006c1800d82001b02003600, 0xd4f001a8201850200820000d36801a65017c920068f400d1d001a1000341800682000d02001a00, 0x194e80228d019d0a00c98806530802060018c9200c8f40191d00321000641800c82001902003200, 0x2945001a62006c7400e8e40001c000e10001c1800382000702000e00, 0xa51400698801d1c800e10001c1800382000702000e00, 0x451400698801b1d004e10009c1801382002702004e00, 0x2d4b00d68a00b50401698802d26805a4a00b4740348e40201c005a1000b41801682002d02005a00, 0x5040019c401135000610000c1800182000302000600, 0x194500726200ac9401692402024001610002c1800582000b02001600, 0x36a2800d31004610008c1801182002302004600, 0x651401c98802b25004a1000941801282002502004a00, 0x1a0a, 0x6a780314e80609c00351a006a2800d32801a620064740068e40101c001a1000341800682000d02001a00, 0x1a0a, 0x1a02, 0x1a9d003534018a4803147001a850035040069a800d1c801a1000341800682000d02001a00, 0x1a02, 0x34f00de8a000cca00198806f1c800610000c1800182000302000600, 0x34c80228a000ce40019b800d31000610000c1800182000302000600, 0x41428082820104c40209280411d00821001041802082004102008200, 0x34f000696004514007a0800131000610000c1800182000302000600, 0x34f000696004514007a0800131000610000c1800182000302000600, 0xd3c008a2800d31000610000c1800182000302000600, 0x0, 0x60e, 0x0, 0x0, 0x220a, 0x6a0801135000610000c1800182000302000600, 0x4741008e7601ccd402398804726808e4a011c740388e40401c008e10011c1802382004702008e00, 0x45140019c400131000610000c1800182000302000600, 0x3145001a620114a402394404028002a1000541800a82001502002a00, 0xc51400698804529004610008c1801182002302004600, 0x8a2800d31002a1000541800a82001502002a00, 0x4f45009e6d013cd402794804f1c809e10013c1802782004f02009e00, 0x34e802282000cec0069a801731000610000c1800182000302000600, 0x34e80228a000cec00b9a800d31000610000c1800182000302000600, 0xd3a008a2800d31000610000c1800182000302000600, 0x220a, 0x2202, 0x229d00453401ca480114680228a00e50c00c9880191d00221000441800882001102002200, 0x2202, 0x34e80068d000d1403b9880751d000610000c1800182000302000600, 0x34d000692004514001a1800131000610000c1800182000302000600, 0x0, 0x0, 0xf28a000cea0019c807929000610000c1800182000302000600, 0x695000d2403d98807b25000610000c1800182000302000600, 0x606, 0x0, 0xd3a001a6800349000610000c1800182000302000600, 0x60a],
  [0x34f80069b000d2e001a4c0034780228b010114001a1c00f41800677000ce60019bc017358006670034c60101880152b802653002c9e00492c0071f800a3b000c2603804800308800010000c1e0300380030680000c000c1602802800304800008000c0e01801801102800004000c0600800800100800000, 0xcae800356801ea9000d0a000a0800d40804080002cca00498400726800a4900046c0008d40001a0002320004620000c00010a00021000041800082000301000200, 0x1208202c0ec0680480100801800e00401800182c0000500200802800c00801008001002000, 0x3628006c1004564001a780034e81e09c000d32006a080e040000676000ce40089b801135000666000cc40018500030800020e000c1800182000302000600, 0xd7a012ae4005590032b1048160001a5402348800a820035020882000213a800671007cd20049840112b000a550000a800294800127000a4d00009800292801b1f003a3d04007800285000508000a0c000c1400282000502000a00, 0xa574001ab400755004ea9054150006a2800342800e82001d020a020000332800e62004cc209818001b29003a510400a0003934007250022490000900038f40071d00023900007000385000708000e0c001c1000381000301000e00, 0x4b180036282e0c400d582019ae40095900069d00c532017a080033b0012750000e80049c80313700066a0004cc004994000320012620024a401593802d2682c04c0024720048500090800060e00241800482000902001200, 0x6574001ab400b55004aa906815001ca2800342801682008d020c820002b35005a690580d000599400b310006610000c000193400b25006e490600900058f400b1d00023900007000585000b0800160c002c1000581000301001600, 0x1a9f07c13c006a6c0014b80669300351e006a2c1c04500028700050601d9dc00d39801a6f0034d600099c02032801a630080c400695c03b2980724f00bc960068fc0051d82203900342610004800d0880401000341e0f003800d0680400c0034160e802803b0480400800340e0d801800d0280400400340607000800100804000, 0xd670006cd08819801fb2400d62801ac1003564001a7800d4e80009c003534006a640204c00469600c524003a380234500028600350a00021000d4100767600f4e40069b800d35001a66000cca10819000d31001a3900342800184800d0800020e00341800682000d02001a00, 0x22ba000d5a001aa400d45000689084110001a14003410006810001000019940033080064d0044920018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1b3800f668000cc003d94001b1803f61004abe00d574013ad8025590002ae003d5a0002b000f55001e92010d14007a18041428460840004c400185800f0a001e10003c1800782000f02001e00, 0x3670006c6004574007ac8041588460b0000d5a001aa8003548000a8000514001a1400341000681098100001994003310006610940c0001934003250022490900900018f40031d0002390000700018500030800060c000c1000181000301000600, 0x1ad4011590022b1010160001a3401744801a820054da0099a40112300224500008800890801120800040001c7c0028e80110a00221000441800181801102002200, 0x5009606c0c41500480300805200e00c01800182c0000500600809c00c01801008001006000, 0x3630006c50b0188001b04011590560b0000d3a001a6400d41000676000ce40019b80033500026600c4c40018500030800220e000c1800182000302000600, 0x1b14039608092b2004d3c001a742e04e009a99012d2201da080033b0026750000e80099c80113700266d0000d80099a8039330006620114ac0239542d02a00124a007c740098500130800060e004c1800982001302002600, 0xc574001ab401555002aa90c4150006a2800342802a82008d0218020004539008e710b40e000a994015310006610000c000a934015250022490000900018f40151d000a390bc07000a85001508002a0c00541000a81000301002a00, 0x1b34017648022b2000d3c00ba740004e002e9a008d2c026a4801147002e8d00011800ba2800743004682005ce400b9b804f3686406c0034c400b85000309002e10005c1800b82001702002e00, 0x3668022ba000d6a001ac80035886a0b0000d3c00ba4804f48864090000d1a001a28003448000880035040019b4003350006690d00d0001954003290022510000a00018f80011d0006390cc0700018500030800060c000c1000181800302000600, 0x229f0e013a008a6c0534b80329300451e0202340114580808a00650e028a0c0113b8096730044de0089ac01133801a630700c401895c0492980324f0024960148fc0051d82403a0044261c80480110880801000441e1b80380110680800c0044161b00280490480800800440e1580180110280800400440604800801900808000, 0x3670022cd000198008b28011648080c8000d8c008b143b062002ec200557c01cae80115b0022b5000168008ac805557004aaa00453c008a680114b00ae9200451c001a343a04600228a00450c021a0800d3100323a000c2c0088500110900221000441800882001102002200, 0x22ba000d721d02e00035a8006b2000d620002c0003468006890035040019b400334800655000ca40089440002800063e0004740018500030800060c000c1000181800302000600, 0x35e8006b9012564001a5400348807682000cbc0019740002e00065a000cb20001600152b002652002c9c0049280030a000610000c1400182000302000600, 0x6c08a0740c41e80480500807800e01401800182c0000500a00809c00c0280100a00100a000, 0x1af40035c8022b2000d2a001a4400d41000675000ce20089580212900024e0084940018500030800060c000c1400182000302000600, 0x6cd000d92001b1404b5900069e000d3a0002700034d000696000d2a0002500034900628e013514005a1803141000676000cea1f01d001735007a62012ca400185000309000610000c1800182000302000600, 0x1af40035c8022b2000d34001a643e04c000695000d24001a440004800068e00ed040019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x6ce000d9a000330003650006c6000d84001af80035e8000bc000d7400aad8039590072ae00d554001a780034b0006950fc12802ba2800f4100666200cc940018580030a000610000c1800182000302000600, 0x1b080036087e0c0000d7a001ae80035c8000b8004564001ab80034a8006910005040019d4003390006710000e00019580112900064e0004940018500030800060c000c1400182000302000600, 0x6c5000d82008ac80033f00067d0000f80019e80033c800078000cec0019c800337002e6a000ccc0069880030a00060e000c1800182000302000600, 0x6e0921000722080480600807800e0180181480280600401800601800800180c0000100c000, 0x8ae8003568006a9000514001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600, 0x3670006cd000198001b28003630006c5000188001b080035f0006ba000d6c00bac800357007eaa000d3c001a744204e00228a0034c40018580030a000610000c1800182000302000600, 0x3650006c9108190001b14003610006c1000180001ae8011590006ae000d3a001a680034c800098000d24001a3800d41000676000ce40019b8011350006660004c40018500030800060e000c1800182000302000600, 0x6a6000d4a000290003510006a1000140001a780034d000696000d24001a3801145000686003d0400698800309000610000c1800182000302000600, 0x4008a10c0922080480700807a00e01c0181500280700401a00601c00800180c0000100e000, 0x8ae8003568006a9003514001a1400340800665000cc20089340032480023d000c720018500030800060c000c1000181000301000600],
  [0x2204f84209b07412e0e024c1604782a08b05011406021c0b0418360770680e60981bc120358140670240c60401881102b82005301c09e03012c0501f80803b0940261200482300880001008001e0f80381e00680000c0640160c00281700480000803c00e0700180d00280000400c00601000801000800000]]

def witT7 : List ℕ := [0x18030001a0641d, 0xc000181d06819, 0x580c0001b06827, 0x18000401d06c1a, 0x4c00030270681b, 0xc0004c1d06c19, 0x30000582706c1a, 0x400004c1d06819, 0x180000c1d0641a, 0x3c00030270681b, 0xc000301e06819, 0x24030301d06819, 0x4c03058270781d, 0x241e06419, 0xc030401b06419, 0x300304c270741e, 0xc000581e06c19, 0xc000301d06819, 0xc0004c1d06819, 0x18000401d0641a, 0x180000c1d06c1a, 0xc00058270781d, 0x4c1b06419, 0xc0004c270741e, 0x18000582706c1a, 0x4006058270781d, 0x40000181d06819, 0x581300c1e07427, 0x1803058270781d, 0x5800030270681b, 0x30090582706c1a, 0x40000301d06819, 0x40000001906419, 0x4c000401d0641a, 0xc000582706c1a, 0xc000301e06419, 0xc00030270681b, 0x24060582706c1a, 0x24030181d06819, 0x24000001906419, 0x4c0000c1d0641a, 0x580304c270741e, 0x18030241e0681d, 0x4c10058270781d, 0x241e0681a, 0x24090241e06419, 0x40100241e07819, 0x300304c2707419, 0x580304c2707419, 0x4c000302706819, 0x58000302706819, 0x1800058270781a, 0xc0304c1b06c19, 0x4c0304c1b06419, 0x300900c1d0641a, 0xc030301a06819, 0x301e07819, 0x30000301e06419, 0x4c1d07419, 0x58000301d06819, 0xc030241a06819, 0x401d07419, 0x580304c2706819, 0x1800058270781d, 0x58000182706819]

def S7 (s i : ℕ) : List ℕ := unpackW wdT7 9 ((levT7.getD s []).getD i 0)

def N7 (s : ℕ) : ℕ := (levT7.getD s []).length

def A7 (s i tag : ℕ) : ℕ := findAct 4096 ((actT7.getD s []).getD i 0) tag

def W7 (w : ℕ) : ℕ := witT7.getD w 0

def Z7 (s : ℕ) := barrier 25 S7 N7 A7 W7 idRot s

theorem enc_inputs7 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT7) = xsT7 := by decide +kernel

theorem enc_goal7 : encL fT7 rowsT7 = goal 25 := by decide +kernel

theorem mask7 : mask 25 = 2 ^ rowsT7.length - 1 := by decide +kernel

theorem proper_fail7 : ∀ zs ∈ xsT7.sublists, zs ≠ xsT7 → (cov 25 zs &&& lo 25) ≠ lo 25 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked7 : ∀ s ≤ 7, ∀ i < N7 s, Z7 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun7 (s : ℕ) (hs : s ≤ 7) (h : NatRun (mask 25) (goal 25) s xsT7) : False := by
  have hc : NatRun (mask 25) (goal 25) 7 xsT7 := extend_run h hs
  have p : xsT7.Perm (S7 7 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked7 7 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub7 : ∀ s ≤ 7, ∀ zs : List ℕ, zs.Sublist xsT7 → NatRun (mask 25) (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT7
  · subst e; exact noRun7 s hs h
  · exact proper_fail7 zs (List.mem_sublists.2 hz) e (required h)

theorem low7 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT7 7 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT7 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 7 h
  have hr : NatRun (mask 25) (encL fT7 rowsT7) s' (ws.map fun a => encL a rowsT7) :=
    Run.map (fun a : BFn 5 => encL a rowsT7)
      (fun a => by rw [mask7]; exact encL_inv a rowsT7)
      (fun a b => encL_and a b rowsT7) (fun a b => encL_or a b rowsT7) hrun
  rw [enc_goal7] at hr
  refine no_sub7 s' (by omega) _ ?_ hr
  rw [← enc_inputs7]
  exact hsub.map _

def mono7 : List Gate := [⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩]

theorem mono_ok7 : ∀ g ∈ mono7, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono7, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval7 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono7, 12⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve7 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaece8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono7, 12, mono_ok7, ?_, mono_eval7⟩
  by_contra hlt
  have hlen : mono7.length = 8 := rfl
  apply low7
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 7
    omega

def rowsT8 : List ℕ := [1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 8, 8, 12, 12, 12, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 5, 9, 17, 6, 10, 7, 11, 19, 5, 6, 9, 10, 13, 14, 28, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT8 : List ℕ := [0x932bce0000e7, 0x12e55f00700f8, 0x274e652387300, 0x3c8f8a5c07c00, 0x3ff8109ff8000]

abbrev fT8 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT8 : List ℕ := [0x7ef6007fff, 0x37075a3f83ff, 0x932bce0000e7, 0x12e55f00700f8, 0x18b19adc78cff, 0x1bf7ffe0700ff, 0x274e652387300, 0x2d1aa0ff8ff07, 0x36cd431ffff18, 0x3c8f8a5c07c00, 0x3ff8109ff8000]

def levT8 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0xb0280701003, 0xb0280901c04, 0xb0280701803, 0xb0280801c03, 0xb0280501003, 0xb01c0400c02, 0xa01c0400c01],
  [0xb0280701003]]

def actT8 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [],
  [0x191d000610000c1800182000302000600, 0x60a, 0xf42801661001c9200c8f40191d00321000641800c82001902003200, 0x60a, 0x60a, 0x602, 0x602],
  [0x69f000d36001a5c0094980068f000d16007a1c00d418006770054e60019bc00335800667002cc600795c0132980124f001c960018fc0051d80403a005c2603004800308800010000c1e0280380030680000c000c160200280090480000800440e01801800302800004000c0600800800100800000]]

def witT8 : List ℕ := [0x2003058270741c, 0x20000401c06c19, 0x58130001a06427, 0x300004c270641a, 0x28000401d06c1a, 0x30000582706819, 0x4c000401c06c19, 0x20000582706819, 0x20000402007019, 0x20050401c06c19, 0x3c00030270641b, 0x20000402a06c19, 0x2000058270741c]

def S8 (s i : ℕ) : List ℕ := unpackW wdT8 9 ((levT8.getD s []).getD i 0)

def N8 (s : ℕ) : ℕ := (levT8.getD s []).length

def A8 (s i tag : ℕ) : ℕ := findAct 4096 ((actT8.getD s []).getD i 0) tag

def W8 (w : ℕ) : ℕ := witT8.getD w 0

def Z8 (s : ℕ) := barrier 25 S8 N8 A8 W8 idRot s

theorem enc_inputs8 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT8) = xsT8 := by decide +kernel

theorem enc_goal8 : encL fT8 rowsT8 = goal 25 := by decide +kernel

theorem mask8 : mask 25 = 2 ^ rowsT8.length - 1 := by decide +kernel

theorem proper_fail8 : ∀ zs ∈ xsT8.sublists, zs ≠ xsT8 → (cov 25 zs &&& lo 25) ≠ lo 25 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked8 : ∀ s ≤ 6, ∀ i < N8 s, Z8 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun8 (s : ℕ) (hs : s ≤ 6) (h : NatRun (mask 25) (goal 25) s xsT8) : False := by
  have hc : NatRun (mask 25) (goal 25) 6 xsT8 := extend_run h hs
  have p : xsT8.Perm (S8 6 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked8 6 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub8 : ∀ s ≤ 6, ∀ zs : List ℕ, zs.Sublist xsT8 → NatRun (mask 25) (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT8
  · subst e; exact noRun8 s hs h
  · exact proper_fail8 zs (List.mem_sublists.2 hz) e (required h)

theorem low8 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT8 6 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT8 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 6 h
  have hr : NatRun (mask 25) (encL fT8 rowsT8) s' (ws.map fun a => encL a rowsT8) :=
    Run.map (fun a : BFn 5 => encL a rowsT8)
      (fun a => by rw [mask8]; exact encL_inv a rowsT8)
      (fun a b => encL_and a b rowsT8) (fun a b => encL_or a b rowsT8) hrun
  rw [enc_goal8] at hr
  refine no_sub8 s' (by omega) _ ?_ hr
  rw [← enc_inputs8]
  exact hsub.map _

def mono8 : List Gate := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [4, 8]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [9, 10]⟩]

theorem mono_ok8 : ∀ g ∈ mono8, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono8, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval8 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono8, 11⟩ (List.ofFn x) =
    Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve8 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeaeee0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono8, 11, mono_ok8, ?_, mono_eval8⟩
  by_contra hlt
  have hlen : mono8.length = 7 := rfl
  apply low8
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 6
    omega

def rowsT9 : List ℕ := [1, 1, 2, 2, 2, 4, 4, 5, 5, 5, 8, 8, 9, 9, 9, 16, 18, 18, 18, 20, 20, 20, 24, 24, 24, 3, 17, 3, 6, 10, 6, 12, 7, 13, 21, 10, 12, 11, 13, 25, 17, 19, 22, 26, 21, 22, 28, 25, 26, 28]

def xsT9 : List ℕ := [0x93e70e007383, 0x12e297a07001c, 0x27457d03803e0, 0x3c8faa1c07c00, 0x3ff8405ff8000]

abbrev fT9 : BFn 5 := fun x : Fin 5 → Bool => Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def wdT9 : List ℕ := [0x7bfa007fff, 0x37055e3f83ff, 0x938404000000, 0x93a50e000000, 0x93e70e007383, 0x12e297a07001c, 0x18ba82fc7fc1f, 0x1bfad7e07001c, 0x27457d03803e0, 0x2d1d685f8ffe3, 0x36c18f1ff8c7c, 0x3c8faa1c07c00, 0x3ff8405ff8000, 0x3ffad7fff801c]

def levT9 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0x300902005, 0x300901804],
  [0xd0300901805, 0xd0300b02406, 0xc0240601403, 0xd0300a02405, 0xe0300901805, 0xd0300701805, 0xd0240601402, 0xc0240601401],
  [0xd0300901805]]

def actT9 : List (List ℕ) :=
  [[],
  [],
  [],
  [],
  [0xd9840192480023d00041800082000102000200, 0x9880012500023a00041800082000102000200],
  [0x9a2800143000610000c1800182000302000600, 0x60a, 0xda24001410032690004c4000954001250016490000900008f40011d00021000041800082000102000200, 0x60a, 0x9a3401345000286004d0a0082100051d002610004c1800982001302002600, 0x60a, 0x602, 0x602],
  [0x34f80069b000d2e001a4c0034780268b010114000a1c02043001283000cee0019cc0033780226b000cce00098c00f2b801a53000c9e00392c0011f800a3b005c2603804800308800010000c1e0300380030680000c00541602802800304800008000c0e01801800b02800004000c0600800800100800000]]

def witT9 : List ℕ := [0x14020281f0741c, 0x80004c1c06819, 0x1c020301f0641c, 0x28020141f0701d, 0x400004c1c06819, 0x28050081d0701f, 0x1c0204c1c06819, 0x8000581d06819, 0x30020581d06819, 0x4c020581f0741c, 0x80004c2207019, 0x80004c2a06819, 0x28020141f0641d, 0x14020281f0641c]

def S9 (s i : ℕ) : List ℕ := unpackW wdT9 9 ((levT9.getD s []).getD i 0)

def N9 (s : ℕ) : ℕ := (levT9.getD s []).length

def A9 (s i tag : ℕ) : ℕ := findAct 4096 ((actT9.getD s []).getD i 0) tag

def W9 (w : ℕ) : ℕ := witT9.getD w 0

def Z9 (s : ℕ) := barrier 25 S9 N9 A9 W9 idRot s

theorem enc_inputs9 : (List.ofFn fun (i : Fin 5) => (fun x : Fin 5 → Bool => x i)).map
    (fun a => encL a rowsT9) = xsT9 := by decide +kernel

theorem enc_goal9 : encL fT9 rowsT9 = goal 25 := by decide +kernel

theorem mask9 : mask 25 = 2 ^ rowsT9.length - 1 := by decide +kernel

theorem proper_fail9 : ∀ zs ∈ xsT9.sublists, zs ≠ xsT9 → (cov 25 zs &&& lo 25) ≠ lo 25 := by
  decide +kernel

set_option maxHeartbeats 40000000 in
theorem checked9 : ∀ s ≤ 6, ∀ i < N9 s, Z9 s i = true := by
  intro s hs
  interval_cases s <;> decide +kernel

theorem noRun9 (s : ℕ) (hs : s ≤ 6) (h : NatRun (mask 25) (goal 25) s xsT9) : False := by
  have hc : NatRun (mask 25) (goal 25) 6 xsT9 := extend_run h hs
  have p : xsT9.Perm (S9 6 0) := by decide +kernel
  exact barrier_all (fun _ {_ _} h => h) checked9 6 le_rfl 0 (by decide +kernel) (Run.perm p hc)

theorem no_sub9 : ∀ s ≤ 6, ∀ zs : List ℕ, zs.Sublist xsT9 → NatRun (mask 25) (goal 25) s zs → False := by
  intro s hs zs hz h
  by_cases e : zs = xsT9
  · subst e; exact noRun9 s hs h
  · exact proper_fail9 zs (List.mem_sublists.2 hz) e (required h)

theorem low9 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 5 fT9 6 := by
  intro h
  obtain ⟨s', hs', ws, hsub, hrun⟩ := exists_run fT9 ⟨fun _ => false, fun _ => true, by decide +kernel⟩ 6 h
  have hr : NatRun (mask 25) (encL fT9 rowsT9) s' (ws.map fun a => encL a rowsT9) :=
    Run.map (fun a : BFn 5 => encL a rowsT9)
      (fun a => by rw [mask9]; exact encL_inv a rowsT9)
      (fun a b => encL_and a b rowsT9) (fun a b => encL_or a b rowsT9) hrun
  rw [enc_goal9] at hr
  refine no_sub9 s' (by omega) _ ?_ hr
  rw [← enc_inputs9]
  exact hsub.map _

def mono9 : List Gate := [⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [7, 10]⟩]

theorem mono_ok9 : ∀ g ∈ mono9, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono9, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem mono_eval9 : ∀ x : Fin 5 → Bool, Circuit.eval ⟨mono9, 11⟩ (List.ofFn x) =
    Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel

theorem solve9 (gates : List Gate) (o : ℕ)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) :
    ∃ (gates' : List Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit 0xfeeafcc8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  refine ⟨mono9, 11, mono_ok9, ?_, mono_eval9⟩
  by_contra hlt
  have hlen : mono9.length = 7 := rfl
  apply low9
  refine ⟨⟨gates, o⟩, ?_, ?_, heval⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hops g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h <;> simp [h]
  · show gates.length ≤ 6
    omega

end PEqualNP.Outside.L_meta_1443

theorem PEqualNP.Outside.L_meta_1443 : ∀ T ∈ ({0xfeeafcc0, 0xeeeaeaea, 0xeeeaeee8, 0xeeeeeee0, 0xfee8eee8, 0xfeeaeaaa, 0xfeeaeae8, 0xfeeaece8, 0xfeeaeee0, 0xfeeafcc8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT gates o hops _ heval
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1443.solve0 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve1 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve2 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve3 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve4 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve5 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve6 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve7 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve8 gates o hops heval
  · exact PEqualNP.Outside.L_meta_1443.solve9 gates o hops heval
